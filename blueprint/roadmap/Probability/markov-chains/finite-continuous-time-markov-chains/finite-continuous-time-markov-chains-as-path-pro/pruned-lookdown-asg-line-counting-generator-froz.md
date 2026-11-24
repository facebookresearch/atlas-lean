# Generator of the pruned lookdown ancestral selection graph line count

Use the two-type model of the [type of the common ancestor under selection and mutation](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/common-ancestor-type-distribution.md) in the convention of Lenz, Kluth, Baake and Wakolbinger: types $0$ (beneficial) and $1$, the diffusion limit of a Moran model in which type $0$ reproduces at relative rate $1+s_N$, with $Ns_N\to\sigma\ge0$, and mutation to type $j$ at rate $u_N\nu_j$, with $Nu_N\to\theta\ge0$ and $\nu_0+\nu_1=1$. The frequency $x$ of type $0$ is then a Wright–Fisher diffusion with drift $(1-x)\theta\nu_0-x\theta\nu_1+\sigma x(1-x)$ and diffusion coefficient $2x(1-x)$. In this convention the ancestral selection graph line count jumps from $k$ to $k-1$ at rate $k(k-1)$ and from $k$ to $k+1$ at rate $k\sigma$.

The pruned lookdown ancestral selection graph has its lines at levels $0,1,\ldots,L$; let $L\in\mathbb N_0$ be the level of its top line (so it has $L+1$ lines). Backwards in time, $L$ is a continuous-time Markov chain on $\mathbb N_0$ with the following transition rates: from $n=0$ the only jump is to $1$, at rate $\sigma$; for $n\ge1$,

$$q(n,n+1)=(n+1)\sigma,\qquad q(n,n-1)=n(n+1)+n\theta\nu_1+\theta\nu_0,\qquad q(n,n-\ell)=\theta\nu_0\quad(2\le\ell\le n),$$

and all other off-diagonal rates are zero. Its total exit rate from $n\ge1$ is $n(n+1)+n\theta+(n+1)\sigma$. Equivalently, for $f:\mathbb N_0\to\mathbb R$ and $n\ge1$,

$$(\mathcal G f)(n)=(n+1)\sigma\,[f(n+1)-f(n)]+\bigl(n(n+1)+n\theta\nu_1\bigr)[f(n-1)-f(n)]+\theta\nu_0\sum_{m=0}^{n-1}[f(m)-f(n)],$$

and $(\mathcal G f)(0)=\sigma\,[f(1)-f(0)]$. The rates are interpreted as follows: branching adds a line at rate $\sigma$ per line, coalescence of two of the $n+1$ lines removes one, a deleterious mutation on one of the $n$ lines other than the immune line removes that line, and a beneficial mutation on the line at level $m<n$ removes all lines above level $m$.

Without mutation ($\theta=0$) the jumps are $n\to n+1$ at rate $(n+1)\sigma$ and $n\to n-1$ at rate $(n+1)n$, so $L+1$ is the ancestral selection graph line count of this convention. Run at half speed, it is the [ancestral selection graph line count](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/realized-asg-line-counting-process-countable-ctm.md) with birth rate $\sigma'k$ and death rate $\binom k2$, where $\sigma'=\sigma/2$.

## Depends on

- [Type of the common ancestor under selection and mutation](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/common-ancestor-type-distribution.md)

## Proof depends on

- [The ancestral selection graph line count as a non-explosive chain](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/realized-asg-line-counting-process-countable-ctm.md)
- [Minimal continuous-time Markov chain on a countable state space](minimal-ctmc-on-a-countable-state-space.md)

## Expansion

A full proof page must establish the following.

- The construction of the lookdown ancestral selection graph and its pruning procedure (deleterious mutations kill non-immune lines; a beneficial mutation at level $m$ kills all higher lines and makes level $m$ the immune line), and that the top level evolves as a Markov chain backwards in time.
- The rates above, including the boundary state $0$, where the downward formula does not apply. The source displays the downward rates for $n\in\mathbb N_0$; they are meaningful only for $n\ge1$, and this restriction is the one consistent with the total exit rate the source uses.
- That the rate matrix is stable and conservative on $\mathbb N_0$, so that it determines a [minimal chain](minimal-ctmc-on-a-countable-state-space.md).
- The reduction without mutation to the ancestral selection graph line count, with the change of time scale and of $\sigma$ between the two conventions.

## Sources

- U. Lenz, S. Kluth, E. Baake, A. Wakolbinger, *Looking down in the ancestral selection graph: a probabilistic approach to the common ancestor type distribution*, Theoretical Population Biology 103 (2015), 27–37, <https://www.techfak.uni-bielefeld.de/ags/bm/publications/Looking_down_ASG.pdf>, Section 2.1 (model and conventions), equation (1) and footnote 4 (ancestral selection graph rates and the conversion to the convention of Krone and Neuhauser), Section 5.2, equation (9) (rates of the pruned lookdown line count) (definitions).
