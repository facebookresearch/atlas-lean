# Pairwise sequentially Markov coalescents SMC and SMC′

For a pair of sequences at constant population size, measure coalescence time in units in which an unordered pair of lineages coalesces at rate $1$. A tree of height $t>0$ has total branch length $2t$. Fix a scaled recombination rate $\rho\ge0$ per unit physical sequence coordinate $x$. Candidate recombination events occur at rate $(\rho/2)(2t)=\rho t$ along the sequence. The starting height has density $\pi(t)=e^{-t}$ on $(0,\infty)$.

At each candidate event, choose $U\sim\mathrm{Unif}(0,t)$, independently of the fresh exponential variables and fair coin below. Use independent random drivers at successive events.

- **SMC:** delete the old branch above the cut before adding the floating lineage. It meets the one remaining lineage at rate $1$, so $K(t,\cdot)$ is the law of $U+Z$, with $Z\sim\mathrm{Exp}(1)$.
- **SMC′:** delete the old branch only after adding the floating lineage. Draw $Z_2\sim\mathrm{Exp}(2)$, where the parameter is the rate. If $U+Z_2<t$, a fair coin selects the own branch (output $t$, a self-transition) or the other branch (output $U+Z_2$). Otherwise output $t+Z$, with a fresh $Z\sim\mathrm{Exp}(1)$. Keep the self-transition as a candidate event.

An explicit kernel representation is

$$K(t,dv)=k(t,v)\,dv,\qquad k(t,v)=\begin{cases}(1-e^{-v})/t,&0<v<t,\\(1-e^{-t})e^{-(v-t)}/t,&v>t,\end{cases}$$

and

$$K'(t,dv)=a(t)\delta_t(dv)+k'(t,v)\,dv,\qquad a(t)=\frac12-\frac{1-e^{-2t}}{4t},\qquad k'(t,v)=\begin{cases}(1-e^{-2v})/(2t),&0<v<t,\\(1-e^{-2t})e^{-(v-t)}/(2t),&v>t.\end{cases}$$

The value of each density at $v=t$ is immaterial; the separate atom is not. These formulas follow by integrating over the uniform cut. For example, below $t$ an SMC′ attachment to the other branch has density $e^{-2(v-U)}\,dv$ conditional on $U<v$, whereas survival to $t$ has probability $e^{-2(t-U)}$. Both kernels have mass one.

## Along-sequence process and invariant laws

Write $K_a$ for either kernel. Construct a process $X_r$, indexed by genetic distance $r$, from the event chain $Y_{j+1}\sim K_a(Y_j,\cdot)$ with independent holding distances $E_j/Y_j$, $E_j\sim\mathrm{Exp}(1)$, retaining candidate self-events. Its generator is

$$ (L_a f)(t)=t\bigl((K_a f)(t)-f(t)\bigr). $$

The process at physical coordinate $x$ is $T_\rho(x)=X_{\rho x}$ and has generator $\rho L_a$. If $\rho=0$ it is constant. This separates a rate per physical length from the accumulated genetic separation $r=\rho x$.

The construction is nonexplosive from every $t>0$. Couple each step so that $Y_{j+1}\le Y_j+Z_j$ with independent $Z_j\sim\mathrm{Exp}(1)$: a downward or self-event needs no increase, and an upward event adds at most its fresh $Z_j$. The [strong law](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md) gives $Y_j\le C(j+1)$ eventually for an almost surely finite $C$. Applied to the independent $E_j$, the same law shows $\sum_j E_j/(j+1)=\infty$: on successive dyadic blocks the sum is bounded below by a quantity tending to $1/2$. Thus the sum of holding distances diverges. All heights stay positive; no uniform distribution on an empty interval or division by a zero height is used.

Both event kernels are reversible with respect to $\mu(dt)=t e^{-t}\,dt$, the $\Gamma(2,1)$ probability law. Indeed, for $0<v<t$, the off-diagonal densities satisfy

$$\mu(t)k(t,v)=\mu(v)k(v,t)=e^{-t}(1-e^{-v}),\qquad \mu(t)k'(t,v)=\mu(v)k'(v,t)=\tfrac12e^{-t}(1-e^{-2v}).$$

The SMC′ diagonal measure is automatically symmetric. Normalization then gives $\mu K=\mu K'=\mu$. Since $t\pi(t)=\mu(t)$, the continuous-distance jump-rate measures satisfy detailed balance for $\pi$. Reversing each finite-event path, including its holding distances, preserves its weight under $\pi$; summing over event counts is exhaustive by nonexplosion. Hence the continuous-distance semigroups are reversible and preserve $\mathrm{Exp}(1)$. This is a semigroup argument, not an inference from $\int L_a f\,d\pi=0$ alone. In particular that integral vanishes for every polynomial $f$, since all relevant mixed moments are finite.

For SMC there is also a direct event-law check: if $T\sim\Gamma(2,1)$ and $V\sim\mathrm{Unif}(0,1)$ independently, then $TV\sim\mathrm{Exp}(1)$, so $TV+Z\sim\Gamma(2,1)$. By contrast, starting an event step from $T\sim\mathrm{Exp}(1)$ gives $\mathbb E[U+Z]=3/2$, not $1$.

For SMC′, removing self-events gives visible-change rate $\rho t(1-a(t))$ and conditional kernel $K'(t,dv)/(1-a(t))$ off the diagonal. Their product is the same off-diagonal rate measure as before. One must not discard the atom while retaining rate $\rho t$. The invariant law of this visible-change chain is proportional to $t e^{-t}(1-a(t))$, whose integral is $2/3$, not to $t e^{-t}$ alone. The event-chain invariant law does not assert that the first future event seen from an arbitrary physical coordinate already has that law.

## Expansion

Separate the kernel definitions, nonexplosion, event-kernel detailed balance, semigroup reversibility and visible-change law into their own statements in a full treatment. The stationary-law argument above applies to both kernels; no simulation is used in place of SMC′ invariance. These are approximations to recombining genealogies, not a claim that the full ancestral recombination graph is Markovian along the chromosome.

## Proof depends on

- [Strong law of large numbers from the ergodic theorem](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md)

## Related topics

- [States of the two-locus ancestral process](two-locus-state.md)

## Sources

- G. A. T. McVean and N. J. Cardin, "Approximating the coalescent with recombination", Philosophical Transactions of the Royal Society B 360 (2005), 1387–1393, <https://doi.org/10.1098/rstb.2005.1673>, Section 3, especially the sequential algorithm's rate $\rho/2$ times total tree length and deletion before reattachment.
- P. Marjoram and J. D. Wall, "Fast \"coalescent\" simulation", BMC Genetics 7 (2006), 16, <https://doi.org/10.1186/1471-2156-7-16>, "The SMC' algorithm", steps 2–5 (each extant branch is met at rate $1$, deletion after reattachment), and the discussion of marginal genealogies and size-biased tree sampling. The explicit densities and detailed-balance proof above are derived from these rules.
