# Projected cone elementary modes are projected elementary modes

**Setting.** A metabolic network with stoichiometric matrix $S \in \mathbb{R}^{m\times n}$ and irreversible reactions $\mathrm{Irr} \subseteq \{1,\dots,n\}$ has steady-state flux cone $C = \{v \in \mathbb{R}^n : Sv = 0,\ v_i \ge 0 \ (i \in \mathrm{Irr})\}$. An *elementary mode* (EM) is $e \in C \setminus \{0\}$ such that no $v \in C\setminus\{0\}$ has $\operatorname{supp}(v) \subsetneq \operatorname{supp}(e)$; up to positive scaling the EMs generate $C$ as a cone. Split the coordinates into $p$ "interesting" reactions $X$ and $q$ others $Y$ ($C \subseteq X \times Y$) and let

$$P_X(C) = \{x \in X : \exists y,\ (x,y) \in C\}$$

be the *projected cone*. When it is pointed (for instance when all reactions are irreversible, so that $P_X(C) \subseteq \mathbb{R}^p_{\ge 0}$), its extreme rays, up to positive scaling, are the *projected cone elementary modes* (ProCEMs); they are not in general the support-minimal vectors of $P_X(C)$. The projections $P_X(e)$ of EMs of $C$ are the *projected elementary modes* (PEMs).

**Theorem.** If all reactions are irreversible, every ProCEM is (up to positive scaling) a PEM: $\mathcal{J} \subseteq \mathcal{P}$.

**Computation (block elimination).** After removing blocked reactions and splitting reversible reactions, write $S' = (A\ B)$ with $A$ the $p$ kept columns and $C = \{(x,y) : Gx + Hy \le 0\}$, where

$$G = \begin{pmatrix} -A \\ A \\ -I_p \\ 0_{q,p}\end{pmatrix}, \qquad H = \begin{pmatrix} -B \\ B \\ 0_{p,q} \\ -I_q\end{pmatrix}.$$

If $r_1,\dots,r_k$ are the extreme rays of the projection cone $W = \{w \ge 0 : H^\top w = 0\}$ and $R = (r_1 \cdots r_k)^\top$, then $P_X(C) = \{x \in \mathbb{R}^p : RGx \le 0\}$, and the ProCEMs are the extreme rays of this cone.

## Expansion

Take a ProCEM $u$ and $v \in C$ with $P_X(v) = u$. Write $v = \sum_k c_k e_k$ with EMs $e_k$ and $c_k > 0$; by linearity $u = \sum_k c_k P_X(e_k)$. Each $P_X(e_k)$ lies in $P_X(C)$, and $u$ spans an extreme ray, so every nonzero $c_kP_X(e_k)$ is a nonnegative multiple of $u$; since $u \ne 0$ some $P_X(e_k)$ is nonzero, hence a positive multiple of $u$, and $u$ is a PEM up to scaling. Support-minimality would not suffice: for three uptakes $x_1, x_2, x_3$ producing $M_1, M_2, M_3$ and drains consuming $M_1 + M_2 + 2M_3$ and $M_1 + 2M_2 + M_3$, $P_X(C) = \operatorname{cone}\{(1,1,2), (1,2,1)\}$ has only full-support nonzero vectors, so $(2,3,3)$ is support-minimal but not a multiple of a PEM. The block-elimination description is Farkas-type: $x$ lies in the projection iff $w^\top Gx \le 0$ for every $w \ge 0$ with $H^\top w = 0$, and it suffices to test the extreme rays of $W$. The converse inclusion fails in general: many PEMs are positive combinations of other PEMs.

## Sources

- S.-A. Marashi, L. David, A. Bockmayr, "Analysis of metabolic subnetworks by flux cone projection", Algorithms for Molecular Biology 7 (2012) 17, Section "Flux cone projection" (Eqs. (1)–(9)) and Theorem 1, <https://doi.org/10.1186/1748-7188-7-17>, PMCID PMC3408373.
