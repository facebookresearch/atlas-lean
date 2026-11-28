# Optimal stabilizing lockdown reduces to matrix balancing

**Setting.** Use the network SIS model and mobility-based mixing matrix $A=CB^\top$ of [Decay-rate certificate for the network SIS model](decay-rate-certificate-for-the-network-sis-model.md). A non-uniform lockdown scales activity at each destination $l$ by $z_l\in(0,1]$ (combining reduced transmission per contact and reduced travel there), giving the post-lockdown matrix

$$A(z)=C\,\mathrm{diag}(z)\,B^\top,$$

with economic cost $c(z)=\sum_lc_l\big(z_l^{-1}-1\big)$, where $c_l>0$ weights location $l$ (for instance its employment); the cost vanishes at $z_l=1$ and blows up under complete closure. Given a target decay rate $\alpha$, the *constrained lockdown problem* minimizes $c(z)$ over $z\in(0,1]^n$ subject to $\lambda_{\max}(\beta A(z)-\gamma I)\le-\alpha$; the *unconstrained* problem drops the upper bound $z_l\le1$ (it may increase activity somewhere). The *high-spread assumption* requires, with the transmission rate absorbed into $C$ and $B$, that $\mathrm{diag}(B^\top C)\ge\gamma$ entrywise: the entry $C_{ii}B_{ii}$ is the spread in location $i$ from same-location trips of its own residents, and it must exceed the recovery rate everywhere.

**Theorem.** Suppose the positive entries of $A$ form a strongly connected graph (and, for the COVID-19 variant, the susceptible fractions are positive).

1. The unconstrained lockdown problem, for the SIS and the two-class COVID-19 network models, reduces to matrix balancing and can be solved in time nearly linear in the number of nonzero entries of $A$.
2. Under the high-spread assumption the constrained and unconstrained problems coincide, so the constrained problem also reduces to matrix balancing.
3. Without the high-spread assumption, when $C=\tau$, $B^\top=D_1\tau^\top D_2$ with $\tau$ strongly connected with positive diagonal, the constrained problem for the SIS, SIR and COVID-19 models is a covering semidefinite program solvable in $\tilde O(n^3)$ time.

Applied to commuting data for the 62 counties of New York State in April 2020, the optimal policy restricts activity more outside New York City than within it, although prevalence was far higher in the city.

## Expansion

A matrix $P=L-D$ with $L\ge0$ and a diagonal $D>0$ is continuous-time stable if and only if $D^{-1}L$ is discrete-time stable, if and only if there is $d>0$ with $D^{-1}Ld\le d$. Since $\lambda_{\max}(C\,\mathrm{diag}(z)B^\top)=\lambda_{\max}(\mathrm{diag}(z)B^\top C)$, the decay constraint becomes the existence of a positive vector certifying that $\mathrm{diag}(z)\,\beta B^\top C/(\gamma-\alpha)$ has spectral radius at most $1$ (for $0\le\alpha<\gamma$). Minimizing $\sum_lc_l/z_l$ under this spectral constraint is a *stability scaling problem*: choose diagonal scalings $q_l=1/z_l$ of minimum weighted sum making $\mathrm{diag}(q)^{-1}P$ stable. Its optimality conditions are exactly those of balancing a positive matrix (finding a diagonal similarity that equalizes row and column sums), for which near-linear time algorithms exist. The box constraint $z_l\le1$ never binds when local transmission is high everywhere, which is part 2; otherwise one obtains a diagonal subtraction problem expressible as a covering semidefinite program.

## Depends on

- [Decay-rate certificate for the network SIS model](decay-rate-certificate-for-the-network-sis-model.md)

## Sources

- Qianqian Ma, Yang-Yu Liu, Alex Olshevsky, "Optimal Lockdown for Pandemic Control", arXiv:2010.12923 (2020): Results (constrained and unconstrained lockdown problems, lockdown cost, post-lockdown matrix, main theoretical contribution, New York State application), Supplementary "Mathematical Background" (covering semidefinite programs, matrix balancing) and "Lockdown Design" (high-spread assumption, splitting lemma, main theorem, stability scaling and diagonal subtraction problems). <https://doi.org/10.48550/arXiv.2010.12923> Published version: IEEE Transactions on Automatic Control 69 (2024) 4538–4553, <https://doi.org/10.1109/tac.2023.3340556>.
