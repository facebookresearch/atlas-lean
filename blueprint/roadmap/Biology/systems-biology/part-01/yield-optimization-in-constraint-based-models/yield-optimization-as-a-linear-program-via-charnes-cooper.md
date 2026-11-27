# Yield optimization as a linear program via the Charnes–Cooper transformation

Let $P = \{ x \in \mathbb{R}^n : A x \le b \}$ be a nonempty flux polyhedron (steady state $Sx = 0$, irreversibilities and any further linear constraints such as uptake bounds, written as inequalities) and let $c, d \in \mathbb{R}^n$. The **yield**

$$Y(x) = \frac{c^{\mathsf T} x}{d^{\mathsf T} x}$$

is defined on $D = \{ x : d^{\mathsf T} x > 0 \}$; typically $c$ weights product fluxes and $d$ substrate uptake fluxes. **Yield optimization** is the linear-fractional program (LFP)

$$\max_{x \in P_{>}} Y(x), \qquad P_{>} = \{ x \in P : d^{\mathsf T} x > 0 \},$$

in contrast to rate optimization $\max_{x \in P} c^{\mathsf T} x$ (flux balance analysis).

**Theorem (LFP-to-LP equivalence).** Define the auxiliary polyhedron

$$P' = \{ (x', t) \in \mathbb{R}^n \times \mathbb{R} : A x' \le t\, b,\ d^{\mathsf T} x' = 1,\ t \ge 0 \}$$

and the LP $\max_{(x', t) \in P'} c^{\mathsf T} x'$. Then:

1. the LFP is feasible iff the LP is feasible, the LFP is unbounded iff the LP is unbounded, and both have the same optimal value (supremum);
2. $x \in P_{>}$ maps to $(x/d^{\mathsf T}x,\ 1/d^{\mathsf T}x) \in P'$ with equal objective, and $(x', t) \in P'$ with $t > 0$ maps back to $x'/t \in P_{>}$ with equal objective;
3. a feasible point $(x', 0)$ is a recession direction of $P$ with $d^{\mathsf T} x' = 1$, and for any $x_0 \in P_{>}$, $Y(x_0 + \lambda x') \to c^{\mathsf T} x'$ as $\lambda \to \infty$. If every optimal LP solution has $t = 0$, the optimal yield is approached but not attained at finite fluxes.

Because $Y(\lambda x) = Y(x)$ for $\lambda > 0$, rate and yield optima differ: if $x_r^*$ and $x_y^*$ are rate- and yield-optimal with positive objective, then $d^{\mathsf T} x_y^* \le d^{\mathsf T} x_r^*$, i.e. yield-optimal states never take up more substrate than rate-optimal ones. With only steady-state and irreversibility constraints the rate LP is unbounded as soon as some flux has $c^{\mathsf T}x > 0$, while the maximal yield is finite unless some flux has $d^{\mathsf T}x = 0 \ne c^{\mathsf T}x$.

## Depends on

- [Optimal value of flux balance analysis](../../stochastic-mass-action-metabolic-control-and-flu/fba-value.md)

## Expansion

This is the Charnes–Cooper substitution $t = 1/d^{\mathsf T} x$, $x' = t x$: it linearizes the ratio because the yield has no constant terms ($p = q = 0$ in the general LFP $(c^{\mathsf T}x + p)/(d^{\mathsf T}x + q)$), so $c^{\mathsf T} x' = Y(x)$ and $A x \le b$ becomes $A x' \le t b$. The only points of $P'$ without a preimage are those with $t = 0$, which are recession directions; along such a ray from any feasible flux the yield converges to the direction's own yield. Numerically, if an LP solver returns $(x^*, 0)$ one maximizes $t$ over $P'$, fixes a small feasible $\tilde t > 0$ and re-optimizes: if the value is unchanged, the optimal yield is attained at finite flux.

## Sources

- S. Klamt, S. Müller, G. Regensburger and J. Zanghellini, "A mathematical framework for yield (vs. rate) optimization in constraint-based modeling and applications in metabolic engineering", Metabolic Engineering (2018), Eqs. (3)–(4), (7)–(15) and Section 2.2.2, <https://doi.org/10.1016/j.ymben.2018.02.001>, PMCID PMC5992331.
- A. Charnes and W. W. Cooper, "Programming with linear fractional functionals", Naval Research Logistics Quarterly 9 (1962) 181–186, <https://doi.org/10.1002/nav.3800090303>.
