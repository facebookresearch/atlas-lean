# Optimal information disclosure in a networked public-goods epidemic game

**Setting.** Individuals are the vertices of a graph $G = (V,E)$, $|V| = n$, with neighbourhoods $N_k$. Individual $k$ chooses a preventive effort $x_k \ge 0$ at marginal cost $c > 0$ and is safe with probability $b(\mathcal{E}_k(x);\iota)$, where $\mathcal{E}_k(x) = x_k + \sum_{j \in N_k} x_j$ is the effort in its closed neighbourhood and $\iota \in \{h,l\}$ is the unknown infection level; $b(\cdot;\iota)$ is increasing and strictly concave with $b(\cdot;h) < b(\cdot;l)$. A government commits to a signalling policy $\pi(\iota_S \mid \iota)$; individuals update a prior $\mu_0$ by Bayes' rule to a posterior belief $\mu = \mu_\pi(h \mid \iota_S)$ and play a Nash equilibrium of the public-goods game with expected utility $\mu\,b(\mathcal{E}_k;h) + (1-\mu)\,b(\mathcal{E}_k;l) - c\,x_k$. The **unilateral effort** $e^\ast(\mu)$ solves

$$\mu\, b'(e^\ast;h) + (1-\mu)\, b'(e^\ast;l) = c,$$

and is assumed increasing in $\mu$. Assume also $c < b'(0;l)$ (the source's Assumption 2: even when certain that the infection level is low, individuals take some positive unilateral effort); the source's Example 2 shows that the theorems below can fail without it. The government picks $\pi$ in an optimistic (best equilibrium) or pessimistic (worst equilibrium) Stackelberg sense.

**Theorem (structure of equilibrium objectives).** Let $\alpha(G)$ be the independence number of $G$.
1. The largest expected aggregate effort over Nash equilibria equals $\alpha(G)\,\mathbb{E}[e^\ast]$, attained by the specialised equilibrium in which a maximum independent set exerts $e^\ast$ and everyone else free-rides.
2. The smallest equals $m(G)\,\mathbb{E}[e^\ast]$ for a graph constant $m(G)$, attained by distributed equilibria when they exist.
3. For the objective "probability that a random individual is safe", the worst equilibrium value is $\mathbb{E}[b(e^\ast_{\iota_S};\iota)]$.

**Theorem (when to disclose).** With absolute risk aversion $\mathcal{A}(Q) = -Q''/Q'$ and prudence $\mathcal{P}(Q) = -Q'''/Q''$, let $\Delta b = b(\cdot;h) - b(\cdot;l)$ and

$$\mathcal{R}(b;\mu) = \mathcal{A}(\Delta b) - \tfrac{1}{2}\mathcal{P}(b), \qquad \tilde{\mathcal{R}}(b;\mu) = \mathcal{A}(\Delta b) - \tfrac{1}{2}\big(\mathcal{P}(b) + \mathcal{A}(b)\big).$$

For the aggregate-effort objective (optimistic or pessimistic government), if $\mathcal{R} > 0$ for all induced beliefs then **no disclosure** is optimal, and if $\mathcal{R} < 0$ for all beliefs then **full disclosure** is optimal; the same holds for the pessimistic safety objective with $\tilde{\mathcal{R}}$ in place of $\mathcal{R}$. If the sign of $\mathcal{R}$ changes once from negative to positive (positive to negative) as $\mu$ increases, exaggerating (downplaying) the infection level is optimal.

## Expansion

By the Bramoullé–Kranton correspondence, specialised equilibria of a public-goods game with concave benefit are exactly the maximal independent sets, each active player exerting $e^\ast$; this collapses every equilibrium objective to a graph constant times a function of the posterior, either $e^\ast(\mu)$ or $b(e^\ast(\mu))$. The government's problem then becomes standard Bayesian persuasion: it chooses a distribution of posteriors with mean $\mu_0$, so the value is the concave envelope of the objective in $\mu$. Differentiating the first-order condition twice gives ${e^\ast}''$ proportional to $b'''\,{e^\ast}' + 2(b''(\cdot;h) - b''(\cdot;l))$, and its sign is that of $-\mathcal{R}$: $e^\ast$ is strictly concave when $\mathcal{R} > 0$ (keep beliefs at the prior, i.e. say nothing) and strictly convex when $\mathcal{R} < 0$ (spread beliefs to the extremes, i.e. reveal everything). Because the network enters only through $\alpha(G)$ or $m(G)$, the optimal signal is independent of the graph, which is what makes the framework scale to heterogeneous networks.

## Sources

- Shraddha Pathak, Ankur A. Kulkarni, "A scalable Bayesian persuasion framework for epidemic containment on heterogeneous networks", Journal of Mathematical Economics 119 (2025), 103134, <https://doi.org/10.1016/j.jmateco.2025.103134>. Published version of arXiv:2207.11578, cited next; locators there refer to the arXiv version.
- Shraddha Pathak, Ankur A. Kulkarni, "A Scalable Bayesian Persuasion Framework for Epidemic Containment on Heterogeneous Networks", arXiv:2207.11578 (2022), Section 3 (Definitions 1–3, Equation for $e^\ast$), Theorem 1, Lemma 1, Theorem 2, Theorem 3 and the proof of Theorem 2 in Section 6, <https://doi.org/10.48550/arXiv.2207.11578>.
