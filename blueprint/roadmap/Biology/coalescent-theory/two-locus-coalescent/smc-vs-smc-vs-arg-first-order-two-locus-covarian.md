# SMC′ matches the two-locus covariance to first order and SMC does not

Let $X_r$ be the stationary [pairwise SMC or SMC′ process](sequentially-markov-coalescent-smc-smc-pairwise.md), indexed by genetic separation $r\ge0$, with $X_0\sim\mathrm{Exp}(1)$ and generator $L_a f(t)=t((K_a f)(t)-f(t))$. Define $C_a(r)=\operatorname{Cov}(X_0,X_r)$. Then

$$C_{\mathrm{SMC}}(r)=1-r+o(r),\qquad C_{\mathrm{SMC}'}(r)=1-\tfrac23r+o(r)\qquad(r\downarrow0).$$

The exact two-locus coalescent started from two linked sequences has covariance $C_{\mathrm{ARG}}(r)=(r+18)/(r^2+13r+18)$ and therefore the same first-order expansion as SMC′. Here the exact model uses recombination rate $r/2$ on each lineage ancestral at both loci and coalescence rate $1$ per pair, as in its [rate matrix](two-locus-rate.md). For a fixed scaled recombination rate $\rho$ per unit physical length, genetic separation is $r=\rho x$; the physical-distance slopes are $-\rho$ and $-2\rho/3$. The generator is not multiplied by $r$ again while also using $r$ as the semigroup time.

## Mean jumps

Let $m_a(t)=\int(v-t)K_a(t,dv)$. For SMC, $\mathbb E[U]=t/2$ and $\mathbb E[Z]=1$, so $m(t)=1-t/2$.

For SMC′ fix a cut $u$ and put $d=t-u$. A self-reattachment changes nothing. Reattachment to the other branch before $t$ contributes $\int_0^d(z-d)e^{-2z}\,dz$, since that branch has rate $1$ while both branches together have rate $2$. Survival to $t$ contributes $e^{-2d}\mathbb E[Z]=e^{-2d}$. The conditional mean jump is therefore $1/4-d/2+(3/4)e^{-2d}$. Averaging $d$ uniformly on $(0,t)$ gives

$$m'(t)=\frac14-\frac t4+\frac{3(1-e^{-2t})}{8t},\qquad t>0.$$

## Justifying the derivative at zero

The right derivative is

$$C'_{a,+}(0)=\langle f,L_a f\rangle_{L^2(\pi)}=\int_0^\infty t^2m_a(t)e^{-t}\,dt,\qquad f(t)=t,\quad\pi(dt)=e^{-t}\,dt.$$

To justify using this unbounded $f$, couple one transition so that $|v-t|\le t+Z$ with $Z\sim\mathrm{Exp}(1)$. Thus the stationary jump-variance integral $\int\pi(dt)\,t\int(v-t)^2K_a(t,dv)$ is at most $\mathbb E[T^3+2T^2+2T]=12$, and $\|L_a f\|_2^2\le\mathbb E[T^2(T+1)^2]=38$. The compensated-jump identity, first localized and then passed to the limit using these bounds and stationarity, gives a square-integrable martingale and
$P_r f-f=\int_0^rP_sL_a f\,ds$ in $L^2(\pi)$. The stationary semigroup is an $L^2$ contraction and is strongly continuous: bounded functions converge at zero by the no-event probability $e^{-rt}$, and truncation gives the general case. Dividing the identity by $r$ proves the displayed derivative formula. Stationarity also fixes both means at $1$, so subtracting their product contributes no derivative.

## Evaluating the slopes

For $T\sim\mathrm{Exp}(1)$, $\mathbb E[T^j]=j!$ and $\mathbb E[Te^{-2T}]=\int_0^\infty t e^{-3t}\,dt=1/9$. Consequently

$$C'_{\mathrm{SMC},+}(0)=2-\tfrac12\,6=-1,$$

and

$$C'_{\mathrm{SMC}',+}(0)=\tfrac14\,2-\tfrac14\,6+\tfrac38(1-1/9)=-\tfrac23.$$

The canonical [path-space covariance theorem](covariance-coalescence-times.md) supplies the actual finite hitting-time covariance for the exact two-locus process, not merely a definition of a rational function. Differentiating it gives $C_{\mathrm{ARG}}(0)=1$ and
$C'_{\mathrm{ARG},+}(0)=(18-13\cdot18)/18^2=-2/3$.

Only the values and right slopes at zero are compared here. Equality of the full SMC′ and ARG covariance curves, or of their processes, does not follow. McVean and Cardin's Section 4(b) quotes $1/(1+r)$ for SMC under the stated assumption that recombination is concentrated at one point between the sites; its slope is consistent with the independent generator calculation above, but that qualifier is not discarded to assert a full-curve identity here.

## Depends on

- [Pairwise sequentially Markov coalescents SMC and SMC′](sequentially-markov-coalescent-smc-smc-pairwise.md)
- [Rate matrix of the two-locus coalescent](two-locus-rate.md)

## Proof depends on

- [Covariance of the coalescence times, path form](covariance-coalescence-times.md)

## Sources

- G. A. T. McVean and N. J. Cardin, "Approximating the coalescent with recombination", Philosophical Transactions of the Royal Society B 360 (2005), 1387–1393, <https://doi.org/10.1098/rstb.2005.1673>, Sections 3 and 4(b), including the concentrated-recombination qualification for $C^*_{ij,ij}$.
- P. Marjoram and J. D. Wall, "Fast \"coalescent\" simulation", BMC Genetics 7 (2006), 16, <https://doi.org/10.1186/1471-2156-7-16>, "The SMC' algorithm". The conditional mean jump, differentiation argument and slope comparison are derived above from the stated kernels.
