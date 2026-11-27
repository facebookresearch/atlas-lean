# Projected cone elementary modes are projected elementary modes

**Setting.** A metabolic network with stoichiometric matrix $S \in \mathbb{R}^{m\times n}$ and irreversible reactions $\mathrm{Irr} \subseteq \{1,\dots,n\}$ has steady-state flux cone $C = \{v \in \mathbb{R}^n : Sv = 0,\ v_i \ge 0 \ (i \in \mathrm{Irr})\}$. An *elementary mode* (EM) is $e \in C \setminus \{0\}$ such that no $v \in C\setminus\{0\}$ has $\operatorname{supp}(v) \subsetneq \operatorname{supp}(e)$; up to positive scaling the EMs generate $C$ as a cone. Split the coordinates into $p$ "interesting" reactions $X$ and $q$ others $Y$ ($C \subseteq X \times Y$) and let

$$P_X(C) = \{x \in X : \exists y,\ (x,y) \in C\}$$

be the *projected cone*. Its elementary modes are the *projected cone elementary modes* (ProCEMs); the projections $P_X(e)$ of EMs of $C$ are the *projected elementary modes* (PEMs).

**Theorem.** If all reactions are irreversible, every ProCEM is (up to positive scaling) a PEM: $\mathcal{J} \subseteq \mathcal{P}$.

**Computation (block elimination).** After removing blocked reactions and splitting reversible reactions, write $S' = (A\ B)$ with $A$ the $p$ kept columns and $C = \{(x,y) : Gx + Hy \le 0\}$, where

$$G = \begin{pmatrix} -A \\ A \\ -I_p \\ 0_{q,p}\end{pmatrix}, \qquad H = \begin{pmatrix} -B \\ B \\ 0_{p,q} \\ -I_q\end{pmatrix}.$$

If $r_1,\dots,r_k$ are the extreme rays of the projection cone $W = \{w \ge 0 : H^\top w = 0\}$ and $R = (r_1 \cdots r_k)^\top$, then $P_X(C) = \{x \in \mathbb{R}^p : RGx \le 0\}$, and the ProCEMs are the extreme rays of this cone.

## Expansion

Take a ProCEM $u$ and $v \in C$ with $P_X(v) = u$. Write $v = \sum_k c_k e_k$ with EMs $e_k$ and $c_k > 0$; by linearity $u = \sum_k c_k P_X(e_k)$. If the nonzero $P_X(e_k)$ are pairwise proportional, $u$ is a PEM. Otherwise $u$ is a positive combination of non-proportional vectors of $P_X(C)$, so it is not an extreme ray, contradicting the fact that in a network with only irreversible reactions the EMs of a pointed cone are exactly its extreme rays. The block-elimination description is Farkas-type: $x$ lies in the projection iff $w^\top Gx \le 0$ for every $w \ge 0$ with $H^\top w = 0$, and it suffices to test the extreme rays of $W$. The converse inclusion fails in general: many PEMs are positive combinations of other PEMs.

## Sources

- S.-A. Marashi, L. David, A. Bockmayr, "Analysis of metabolic subnetworks by flux cone projection", Algorithms for Molecular Biology 7 (2012) 17, Section "Flux cone projection" (Eqs. (1)–(9)) and Theorem 1, <https://doi.org/10.1186/1748-7188-7-17>, PMCID PMC3408373.
