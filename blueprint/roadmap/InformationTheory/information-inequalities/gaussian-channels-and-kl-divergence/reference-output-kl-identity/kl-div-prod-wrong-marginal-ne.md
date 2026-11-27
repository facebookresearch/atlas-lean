# Kl Div prod wrong marginal ne

The reference-output decomposition needs the actual output marginal in its middle term. On $\{\mathrm{true}, \mathrm{false}\}^2$, let $\mu = \delta_{(\mathrm{true}, \mathrm{true})}$, whose marginals are both $\delta_{\mathrm{true}}$, and take the reference $Q = \delta_{\mathrm{true}}$. Replacing the output marginal by $\delta_{\mathrm{false}}$ breaks the identity:

$$D_{\mathrm{KL}}(\mu \parallel \delta_{\mathrm{true}} \otimes \delta_{\mathrm{true}}) \ne D_{\mathrm{KL}}(\mu \parallel \delta_{\mathrm{true}} \otimes \delta_{\mathrm{false}}) + D_{\mathrm{KL}}(\delta_{\mathrm{false}} \parallel \delta_{\mathrm{true}}),$$

since the left side is $0$ and the right side is $+\infty$.
