# Reproduction number of app-based digital contact tracing

In a homogeneously mixing population of size $n$, a Markovian SIR epidemic has contact rate $\beta$, natural recovery rate $\gamma$ and diagnosis rate $\delta$, so without tracing $R_0 = \beta/(\gamma+\delta)$. Each individual independently uses a tracing app with probability $\pi \in (0,1]$. When an infectious app-user is diagnosed, all app-using contacts (infector and infectees) are instantly traced, tested and isolated, and those who were infected trigger tracing among their own app-using contacts, and so on.

1. **Branching limit.** Started from one infective, the epidemic converges on finite time intervals, as $n \to \infty$, to a limit process. The limit is not a branching process in individuals, but it is a two-type branching process in macro-individuals: type 1 is an app-using component (a maximal transmission chain of app-users) and type 2 is a non-app-user.
2. **Reproduction number.** The limit is supercritical if and only if $R_D > 1$, where $R_D$ is the largest eigenvalue of the two-type next-generation matrix,

    $$R_D = \frac{R_0(1-\pi)}{2} + \sqrt{\frac{(R_0(1-\pi))^2}{4} + f(\pi)\,R_0\,\pi}, \qquad f(\pi) = \frac{1-\pi}{2\pi\delta}\Bigl(\beta\pi - \gamma - \delta + \sqrt{(\beta\pi+\gamma+\delta)^2 - 4\beta\pi\gamma}\Bigr).$$

    If $R_D > 1$, the final number infected tends to infinity with positive probability; if $R_D \le 1$, the final fraction infected tends to $0$ in probability.

3. **Combined tracing.** With manual tracing added (each contact of a diagnosed individual traced independently with probability $p$), the epidemic converges on finite time intervals to a limit process that is a two-type branching process in to-be-traced components, rooted at an app-user or at a non-app-user. With $R_{DM}$ the largest eigenvalue of its mean-offspring matrix, the final number infected tends to infinity with positive probability if $R_{DM} > 1$, and the final fraction infected tends to $0$ in probability if $R_{DM} \le 1$.

## Expansion

Tracing creates dependence along app-user chains, because an app-user can be traced through its infector or through any of its infectees. Grouping a whole app-using chain into one macro-individual removes the dependence, since tracing never crosses between a component and a non-app-user. The component starts from an app-user root and grows as a birth process at rate $\beta\pi$ per infective, and the whole component is removed at the first diagnosis. Its mean offspring count gives $f(\pi)$, and $R_D$ is the Perron root of the resulting $2\times2$ matrix.

## Sources

- Tom Britton and Dongni Zhang, "Epidemic models with digital and manual contact tracing", Advances in Applied Probability 57 (2025), 1430–1455, <https://doi.org/10.1017/apr.2025.15>; numbering as in arXiv:2211.12869: Section 3 (main results: the limit-process proposition and its corollary for digital tracing, the proposition and corollary for the combined model in Section 3.2, and the three theorems comparing critical fractions and the individual reproduction number) and Section 5.
