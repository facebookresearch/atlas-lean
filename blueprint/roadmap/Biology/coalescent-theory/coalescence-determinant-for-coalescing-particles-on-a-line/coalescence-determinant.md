# Coalescence determinant for coalescing particles on a line

**Setting.** Let the state space $S$ be $\mathbb R$ or $\mathbb Z$ with reference measure $\nu$ (Lebesgue or counting measure). A single particle moves as a Markov process satisfying the Karlin–McGregor hypotheses: strong Markov, with continuous paths on $\mathbb R$ or nearest-neighbour moves on $\mathbb Z$, so that two particles cannot change order without meeting. Fix a horizon $T>0$ and write $p_x(y)$ for the density of the position at time $T$ of a particle started at $x$, and $F_x(y)=\mathbb P_x(X_T\le y)$ for its distribution function. Start $n$ particles at $x_1<\cdots<x_n$. They move independently, and when two adjacent particles meet they coalesce into one particle that continues with the same dynamics (coalescing random walks or coalescing Brownian motions).

A *coalescence pattern* at time $T$ is a composition $c_1+\cdots+c_k=n$: the first $c_1$ particles have merged into survivor $1$, the next $c_2$ into survivor $2$, and so on, with survivors at ordered positions $y_1<\cdots<y_k$.

**Coalescence matrix.** Index rows by $i\in\{1,\dots,n\}$ and columns by $j\in\{1,\dots,n\}$, the columns grouped into consecutive blocks of sizes $c_1,\dots,c_k$. If column $j$ lies in block $l$,
$$\widetilde M_{ij}=\begin{cases}p_{x_i}(y_l)&\text{if $j$ is the first column of its block},\\ F_{x_i}(y_l)-\mathbf 1[i<j]&\text{otherwise.}\end{cases}$$

**Statement.** For every measurable $A\subseteq W_k=\{(y_1,\dots,y_k)\in S^k:y_1<\cdots<y_k\}$,
$$\mathbb P\bigl(\text{the pattern at time $T$ is }(c_1,\dots,c_k)\text{ and the survivors' positions lie in }A\bigr)=\int_A\det\widetilde M(y_1,\dots,y_k)\,\nu^{\otimes k}(\mathrm dy).$$
So $\det\widetilde M$ is the joint density (continuous case) or mass function (discrete case) of the survivors for the given pattern. With every $c_l=1$ it is the Karlin–McGregor determinant $\det[p_{x_i}(y_j)]$ for non-colliding particles.

**Example.** For two particles merging ($n=2$, $k=1$), $\det\widetilde M=p_{x_1}(y)F_{x_2}(y)+p_{x_2}(y)\bigl(1-F_{x_1}(y)\bigr)$. Integrating over $y$ gives $2\,\mathbb P(X^{(2)}_T<X^{(1)}_T)$ for two independent copies, the reflection-principle probability that the two paths have met by time $T$.

## Depends on

- [Coalescing random walks dual to the voter model on a finite graph](../structured-coalescent/coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

The proof restores a fixed particle number: at each collision one survivor continues and an invisible *ghost* particle is created next to it, carrying a sign that records whether it ends left or right of its survivor. With ghosts, the probability of a pattern together with all final positions (survivors and ghosts) is an $n\times n$ determinant whose survivor columns hold transition probabilities and whose ghost columns hold signed, staircase-masked transition probabilities; the proof is a Lindström–Gessel–Viennot-type sign-reversing involution on path families. Integrating each ghost over the half-line selected by its sign and summing over signs turns the ghost columns into the cumulative columns $F_{x_i}(y_l)-\mathbf 1[i<j]$. Through voter-model duality, the formula gives exact finite-time laws of cluster boundaries; in reaction–diffusion language it is the exact law of the coalescence reaction $A+A\to A$ on a line.

## Sources

- P. Śniady and Á. Urbán, *Exact determinant formulas for coalescing particle systems*, arXiv:2602.10782 (2026): the coalescence formula with ghosts (Section "The main result and an overview of its proof"), its continuous-time form (Section "Continuous processes"), and the coalescence determinant with the coalescence matrix (Section "Integrating out the ghosts"). <https://doi.org/10.48550/arXiv.2602.10782>
