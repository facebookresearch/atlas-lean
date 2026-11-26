# ILP group test for paths safe in every minimum flow decomposition

**Setting.** Let $G=(V,E,f)$ be a flow network on a directed acyclic graph with source $s$, sink $t$ and positive integer flows. A **minimum flow decomposition** (MFD) writes $f$ as $\sum_{i=1}^k w_i\,\mathbf 1_{P_i}$ with $s$-$t$ paths $P_i$, weights $w_i\in\mathbb Z_{>0}$, and $k$ minimum. A path $P$ is **safe** for MFD if in every MFD $P$ is a subpath of some $P_i$; it is **maximal safe** if no strictly longer safe path contains it. (For decompositions of any size, $P$ is safe if and only if its excess flow, the flow on its first edge minus the flow leaving its internal nodes off $P$, is positive.)

Let $\mathcal M$ be any feasible ILP whose solutions are exactly the MFDs of size $k$, with binary variables $x_{uvi}$ indicating that edge $(u,v)$ lies on path $i$.

**Group test.** For a set $\mathcal P$ of paths, add binaries $\gamma_P$ ($P\in\mathcal P$) and, for every $P = (v_1,\dots,v_\ell)\in\mathcal P$ and every $i\in\{1,\dots,k\}$, the constraint

$$
x_{v_1v_2i} + x_{v_2v_3i} + \cdots + x_{v_{\ell-1}v_\ell i} \le \ell - 1 - \gamma_P ,
$$

and maximize $\sum_{P\in\mathcal P}\gamma_P$. Let $\mathcal N=\{P:\gamma_P=1\}$ at an optimum. Then: (1) if $\mathcal N=\emptyset$, every path in $\mathcal P$ is safe; (2) otherwise every path in $\mathcal N$ is unsafe, and $\mathcal N$ is a largest set of paths of $\mathcal P$ simultaneously avoidable by one MFD. Recursing on $\mathcal P\setminus\mathcal N$ classifies all of $\mathcal P$ with at most $|\mathcal P|+1$ ILP calls, and is used inside top-down (shrink unsafe paths) or bottom-up (extend safe paths) searches for all maximal safe paths.

**Theorem (hardness).** There is a polynomial-time Turing reduction from UNIQUE 3SAT (3SAT instances with exactly one satisfying assignment) to MFD-SAFETY, the problem of deciding whether a given path is safe for MFD. Hence MFD-SAFETY is NP-hard under randomized reductions.

## Expansion

Because solution paths repeat no node, $P$ is contained in path $i$ exactly when all $\ell-1$ of its edges are selected for $i$; the constraint with $\gamma_P=1$ forbids that for every $i$, so $\gamma_P=1$ is feasible exactly when some MFD avoids $P$. An optimum of $0$ therefore certifies that no single path of $\mathcal P$ can be avoided. For hardness, use the Hartman et al. reduction from 3SAT to MFD: in any MFD of the target size each variable gadget carries a weight-$4$ path up either its left side (TRUE) or right side (FALSE). Query the safety of both side paths of every gadget; with a unique satisfying assignment exactly one side per variable is safe, and the induced assignment can be checked clause by clause. With several satisfying assignments some variable has no safe side, and unsatisfiable instances fail the clause check, so the procedure decides UNIQUE 3SAT.

## Sources

- F. H. C. Dias, M. Cáceres, L. Williams, B. Mumey and A. I. Tomescu, "A safety framework for flow decomposition problems via integer linear programming", arXiv:2301.13245 (2023), Section 2 (safety test, Eq. for $\gamma_P$ constraints and the GetSafe recursion) and appendix "Hardness of Testing MFD Safety" (Theorem 1), <https://doi.org/10.48550/arXiv.2301.13245>.
