# Ancestral selection graph duality and ancestral types under pairwise interaction

**Setting.** Let $y(t;y_0)$ solve the two-type mutation–selection equation with pairwise interaction

$$\dot y=-y(1-y)\big[s+\gamma(1-y)\big]+u\nu_1(1-y)-u\nu_0y,$$

the law-of-large-numbers limit of a Moran model of size $N$ in which, besides neutral resampling, a type-0 (fit) individual reproduces selectively at rate $s$ and interactively at rate $\gamma$ if a random partner is also fit, and mutation happens at rate $u$. Tracing a sampled individual backwards gives the *embedded ancestral selection graph* (eASG): a random tree whose vertices branch in two at rate $s$ (potential selective parents), in three at rate $\gamma$ (potential interactive parent and partner), and are marked by mutations at rate $u$. Given iid Bernoulli($y_0$) types at the leaves, types propagate to the root by the rule: at a binary branching the vertex is of type $1$ iff both children are; at a ternary branching it is of type $1$ iff the continuing child is of type $1$ and at least one of the two other children is of type $1$; a mutation mark to type $1$ (resp. $0$) forces type $1$ (resp. $0$). Let $H(\alpha,y_0)$ be the probability that the root of a tree $\alpha$ receives type $1$.

**Theorem (duality).** For every tree $\alpha$ and $t\ge0$, $H\big(\alpha,y(t;y_0)\big)=\mathbb E_\alpha[H(\alpha_t,y_0)]$, where $(\alpha_t)$ is the eASG process; in particular $y(t;y_0)=\mathbb E[H(\alpha_t,y_0)]$ starting from a single line. The same duality holds for the pruned ASG (cut at mutations) and for its stratified tripod-tree version.

**Theorem (stochastic representation of equilibria).** For the stratified ASG started from one line, $H(\mathscr T_t,y_0)$ converges almost surely to a limit $H_\infty(y_0)$; if $y_0$ is not an unstable interior equilibrium, $H_\infty(y_0)$ is Bernoulli with parameter $y_\infty(y_0)=\lim_t y(t;y_0)$. The smallest and largest equilibria $y_{\min}\le y_{\max}$ in $[0,1]$ (not necessarily attracting: in the source's region $\Theta_2^a$, where $\nu_0=0$, $y_{\min}=\bar y_-$ is stable and $y_{\max}=1$ is unstable) equal the probability that the stratified ASG is absorbed in the state $0$ (the tree reduced to a root of weight $0$: every line has been pruned by a deleterious mutation, so the root is unfit and $H=1$) and the probability that it is never absorbed in the cemetery state $\Delta$ (reached at a beneficial mutation, which makes the root fit and $H=0$), respectively.

**Theorem (ancestral type distribution, $\nu_0=0$).** Let $g_r(y_0)$ be the probability that the ancestor, $r$ time units back, of an individual sampled today is of type $1$, when the type-1 frequency at that past time is $y_0$. Then

$$g_r(y_0)=y_0\exp\!\Big(-\int_0^r\big(1-y(\xi;y_0)\big)\big(s+\gamma(1-y(\xi;y_0))\big)\,d\xi\Big),$$

and $g_\infty(y_0)=\lim_{r\to\infty}g_r(y_0)$ exists. At equilibrium, $g_\infty(y_\infty(1))=1$, and for $y_0\in[0,1)$: $g_\infty(y_\infty(y_0))=1$ in the extinction region, $=0$ in the region where the fit type persists from any positive frequency, and in the bistable region it equals $0$ if $y_0\le\bar y_+$ and $1$ if $y_0>\bar y_+$.

## Expansion

The duality follows by checking that the generator of the eASG applied to $H(\cdot,y_0)$ equals the drift of the ODE times $\partial_{y_0}H$: a binary branching contributes $-sy_0(1-y_0)\partial H$, a ternary one $-\gamma y_0(1-y_0)^2\partial H$, and mutations $u\nu_1(1-y_0)\partial H$ (to type $1$) and $-u\nu_0y_0\partial H$ (to type $0$). For the ancestral type, the root's ancestral line ("immune line") has binary and ternary side branches arriving as independent Poisson processes of rates $s$ and $\gamma$; the ancestor is unfit iff the line's own leaf is unfit and no side branch pre-empts it, and averaging over the side branches with the duality gives the exponential factor.

## Depends on

- [Equilibria of the mutation–selection equation with pairwise interaction](equilibria-of-the-mutation-selection-equation-with-pairwise-interaction.md)

## Sources

- Ellen Baake, Fernando Cordero and Sebastian Hummel, "Lines of descent in the deterministic mutation–selection model with pairwise interaction", *Ann. Appl. Probab.* 32(4) (2022), 2400–2447. <https://doi.org/10.1214/21-AAP1736>
- Preprint version (the locators in this item follow its numbering): Ellen Baake, Fernando Cordero, Sebastian Hummel, "Lines of descent in the deterministic mutation-selection model with pairwise interaction", arXiv:1812.00872: Proposition 2.7 (law of large numbers), Theorem 2.10 (eASG duality), Corollary 2.17 (pruned ASG duality), Theorem 2.22 (stratified ASG duality), Theorem 2.25 and Corollary 2.26 (stochastic representation of equilibria), Theorem 2.32 and Corollary 2.33 (ancestral type distribution), Lemma 4.3 (generator identities). <https://doi.org/10.48550/arXiv.1812.00872>
