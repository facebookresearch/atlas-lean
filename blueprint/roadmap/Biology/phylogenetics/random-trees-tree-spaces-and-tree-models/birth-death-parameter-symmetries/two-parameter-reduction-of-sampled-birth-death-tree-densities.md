# Two-parameter reduction of sampled birth–death tree densities

Consider a birth–death process with birth rate $\lambda>0$ and death rate $\mu\ge 0$, started from one individual and stopped after time $t_0$, in which each extant individual is sampled independently with probability $\rho\in(0,1]$. Let $\mathcal T$ be the reconstructed tree on the $n$ sampled tips with branching times $t_1>\dots>t_{n-1}$ before the present. For $\lambda\ne\mu$ and $r=\lambda-\mu$,

$$p_{1,1}(t)=\frac{\rho\,r^2e^{-rt}}{\bigl(\rho\lambda+(\lambda(1-\rho)-\mu)e^{-rt}\bigr)^2},\qquad 1-p_0(t)=\frac{\rho\,r}{\rho\lambda+(\lambda(1-\rho)-\mu)e^{-rt}},$$

are the probabilities that one lineage has exactly one, respectively at least one, sampled descendant after time $t$; the unconditioned density is $f(\mathcal T\mid L(t_0)=1)=p_{1,1}(t_0)\prod_{i=1}^{n-1}\lambda\,p_{1,1}(t_i)$. It depends on all three parameters: already for a one-tip tree it is $p_{1,1}(t_0)$, which is not a function of $(\lambda',\mu')$ below.

Define

$$\lambda'=\rho\lambda,\qquad \mu'=\mu-\lambda(1-\rho),$$

so $\lambda'-\mu'=\lambda-\mu$, and $\mu'$ may be negative.

**Theorem.**
1. The functions $\lambda(1-p_0)$, $\lambda p_{1,1}$, $\lambda q$ and $\lambda p_n$ (where $p_n=p_{1,1}(\lambda q)^{n-1}$ for $n>1$) depend on $(\lambda,\mu,\rho)$ only through $(\lambda',\mu')$, and through $\lambda'$ alone when $\lambda=\mu$. Consequently each of the conditioned reconstructed-tree densities depends only on $(\lambda',\mu')$: given the stem age $t_0$ (the process started from one lineage), conditioned on at least one sampled tip or on exactly $n$ sampled tips; and given the crown age (two lineages at the first split), conditioned on both crown subtrees having a sampled tip or on exactly $n$ sampled tips. Fixing the process age alone, without one of these conditionings, does not give the reduction.
2. In these coordinates, with $\tilde p_0=(1-p_0)/\rho$ and $\tilde q=q/\rho$, the birth–death symmetries hold: $\lambda'(1-\tilde p_0(t\mid\lambda',\mu'))=\mu'(1-\tilde p_0(t\mid\mu',\lambda'))$, $\tilde p_0(t\mid\lambda',\mu')=\tilde p_0(t\mid\mu',\lambda')e^{(\lambda'-\mu')t}$, $\tilde q(t\mid\lambda',\mu')=\tilde q(t\mid\mu',\lambda')$, and $(\mu')^{n-1}\tilde p_n(t\mid\lambda',\mu')=(\lambda')^{n-1}\tilde p_n(t\mid\mu',\lambda')$ for $n\ge 1$.
3. Two triples $(\lambda,\mu,\rho)$ and $(\hat\lambda,\hat\mu,\hat\rho)$ give the same conditioned tree densities (each of the densities of item 1) whenever $\lambda\rho=\hat\lambda\hat\rho$ and $\mu-\lambda(1-\rho)=\hat\mu-\hat\lambda(1-\hat\rho)$. Such a $(\hat\lambda>0,\hat\mu\ge 0)$ exists for every $\hat\rho\in(0,1]$ if $\mu/\lambda\ge 1$, and for $0<\hat\rho\le\rho/(1-\mu/\lambda)$ if $\mu/\lambda<1$.
4. In particular (Stadler and Steel 2012), with $\mu/\lambda<1$ an equivalent complete-sampling model ($\hat\rho=1$) exists if and only if $\mu/\lambda\ge 1-\rho$.

## Proof depends on

- [Waugh's birth–death interchange symmetry](waugh-s-birth-death-interchange-symmetry.md)

## Expansion

Item 1 is direct algebra: multiplying numerator and denominator of each expression by $\lambda$ turns $\rho\lambda$ into $\lambda'$ and $\lambda(1-\rho)-\mu$ into $-\mu'$, while $r=\lambda'-\mu'$. Conditioning divides by survival probabilities of the same form, so conditioned densities are functions of $(\lambda',\mu')$. Item 2 is Waugh's interchange symmetry transported to these coordinates. For item 3, inverting the map gives $\hat\lambda=\lambda'/\hat\rho$ and $\hat\mu=\mu'-\lambda'+\lambda'/\hat\rho$, and $\hat\mu\ge 0$ is the stated constraint on $\hat\rho$. Thus the sampling fraction cannot be estimated from a reconstructed tree with these conditioned likelihoods, and an estimate with $\mu'<0$ cannot be explained by complete sampling: properties of complete-sampling tree distributions extend to sampled trees only when $\mu/\lambda\ge 1-\rho$.

## Sources

- T. Stadler and M. Steel, "Swapping birth and death: symmetries and transformations in phylodynamic models", Systematic Biology 68(5) (2019) 852–858, <https://doi.org/10.1093/sysbio/syz039>, PMCID PMC6701459. Theorem 2, Lemma 3, Theorems 4, 5, 7 and 8, Corollaries 9–10.
