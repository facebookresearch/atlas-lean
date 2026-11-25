# Difference-in-differences estimand

For a measure space $(\Omega, \mu)$, a treated group $G \subseteq \Omega$ and outcomes $Y_{\mathrm{pre}}$, $Y_{\mathrm{post}}$, the two-by-two difference-in-differences estimand is

$$\langle Y_{\mathrm{post}} - Y_{\mathrm{pre}}\rangle_G - \langle Y_{\mathrm{post}} - Y_{\mathrm{pre}}\rangle_{G^c},$$

where $\langle f\rangle_A$ is the average of $f$ over $A$ (taken to be $0$ if $\mu(A) \in \{0, \infty\}$ or $f$ is not integrable on $A$). For a probability measure with $0 < \mu(G) < 1$ and integrable outcomes these are the conditional means given the group.

## Sources

- J. Roth, P. H. C. Sant'Anna, A. Bilinski and J. Poe, "What's trending in difference-in-differences? A synthesis of the recent econometrics literature", *Journal of Econometrics* 235 (2023), 2218–2244.
