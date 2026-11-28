# Forward-backward coalescent of the substitution Fleming–Viot process

**Model.** Clonal individuals carry an ecological trait $x\in\mathcal X\subset\mathbb R^d$ and a neutral marker $u\in\mathcal U\subset\mathbb R^q$. An individual with trait $x$ gives birth at rate $b(x)$, dies at rate $d(x)+\sum_y C(x,y)\,n(y)/K$ (logistic competition with kernel $C$, carrying-capacity scale $K$), trait mutations are rare and marker mutations are frequent but small. Three timescales emerge as $K\to\infty$.

1. *(Ecological timescale.)* Strain densities with traits $x_1,\dots,x_p$ follow the competitive Lotka–Volterra system

$$
\frac{dn_t(x_j)}{dt}=\Big(b(x_j)-d(x_j)-\sum_{\ell=1}^pC(x_j,x_\ell)\,n_t(x_\ell)\Big)n_t(x_j).
$$

   If $\eta(x_i)C(x_i,x_j)$ is symmetric and positive definite for some positive weights $\eta$, every positive solution converges to a unique stable equilibrium $\hat n(\cdot\,;x_1,\dots,x_p)$.
2. *(Evolutionary timescale: polymorphic evolution sequence, PES.)* A mutant trait $y$ arising from strain $x_j$ invades with probability $[f(y;x_1,\dots,x_p)]_+/b(y)$, where

$$
f(y;x_1,\dots,x_p)=b(y)-d(y)-\sum_{j}\hat n(x_j;x_1,\dots,x_p)\,C(y,x_j)
$$

   is its invasion fitness; the trait distribution then jumps to the new Lotka–Volterra equilibrium.
3. *(Marker timescale.)* Between adaptive jumps, the marker distribution $F_t(x,dv)$ within strain $x$ is a Fleming–Viot process with mutation generator $A$ and resampling variance $2b(x)/\hat n(x;\cdot)$, so the strain's effective size is $N_e(x)=\hat n(x;x_1,\dots,x_p)$, which depends on the whole community through competition. The joint limit is a superprocess whose trait marginal is the PES (the *substitution Fleming–Viot process*).

**Theorem (genealogies).** For $n$ individuals sampled from a strain at time $t$, with adaptive jump times $T_0=0<T_1<\dots<T_J\le t$:

1. on each interval $[T_k,T_{k+1})$ the genealogy within strain $x_i$ is a Kingman coalescent run at pairwise coalescence rate $2b(x_i)/\hat n(x_i;x_1,\dots,x_p)$, with the trait set of that interval;
2. at the jump time when strain $x_i$ was founded, all its surviving lineages merge instantaneously into the single founding mutant (a multiple merger);
3. moment duality holds: for every $\zeta_0\in C(\mathcal U^n,\mathbb R)$ such that, for each $i\in\{1,\dots,n\}$ and all fixed $(u_1,\dots,u_{i-1},u_{i+1},\dots,u_n)\in\mathcal U^{n-1}$, the section $u_i\mapsto\zeta_0(u_1,\dots,u_n)$ lies in the domain $D(A)$ of the mutation generator $A$, $\mathbb E_{\pi_0}\langle\pi_t^{\otimes n},\zeta_0\rangle=\int\mathbb E_{(u_1,\dots,u_n)}\zeta_0(U_t^1,\dots,U_t^n)\,\pi_0^{\otimes n}(du)$, where $(U^i)$ move by the mutation generator and copy each other's states pairwise (Kingman resampling).

## Depends on

- [Kingman's coalescent](../../coalescents/merger-rate-dirac-zero.md)
- [Fleming–Viot well-posedness on a compact type space](../../../population-genetics/diffusion-theory/fleming-viot-processes/fleming-viot-well-posedness-on-a-compact-type-sp.md)

## Expansion

The genealogy is built *forward-backward*: the trait tree (PES) is generated forward in time because which mutants invade depends on the current community, and marker genealogies are then generated backward within the piecewise-constant trait structure. Because effective sizes are equilibrium densities of a competitive community, genealogical branch lengths and genetic diversity carry information about birth rates, competition kernels and the ecological history, not just about an exogenous demography. Instantaneous multiple mergers at founding events reflect that each new strain stems from one mutant and that fixation is fast on the evolutionary timescale. The model is used as the simulator in approximate Bayesian computation, with phylogenetic summary statistics, to infer jointly ecological, demographic and genetic parameters, including in the Dieckmann–Doebeli model of adaptive diversification.

## Sources

- Clotilde Lepers, Sylvain Billiard, Matthieu Porte, Sylvie Méléard, Viet Chi Tran, "Inference with selection, varying population size, and evolving population structure: application of ABC to a forward–backward coalescent process with interactions", *Heredity* 126 (2021), 335–350, <https://doi.org/10.1038/s41437-020-00381-x>; preprint arXiv:1910.10201 (2019), Section 2 (model, effective size, forward-backward coalescent), Appendix A (Propositions A.1–A.2, Definitions A.3–A.4, Theorem A.5, Lemma A.6, Proposition A.7), <https://doi.org/10.48550/arXiv.1910.10201>.
