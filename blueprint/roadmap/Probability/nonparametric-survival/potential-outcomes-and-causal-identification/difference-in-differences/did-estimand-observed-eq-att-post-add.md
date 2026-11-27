# Bias decomposition of difference in differences

Let $(\Omega, \mu)$ be a measure space, $G \subseteq \Omega$ a measurable treated group, and for a function $f$ and a set $A$ write $\langle f\rangle_A$ for the average of $f$ over $A$ (taken to be $0$ if $\mu(A) \in \{0, \infty\}$ or $f$ is not integrable on $A$). Let $Y_{\mathrm{pre}}(d), Y_{\mathrm{post}}(d)$ be potential outcomes for $d \in \{0, 1\}$, integrable on $G$ (for $Y_{\mathrm{pre}}(0)$, $Y_{\mathrm{post}}(0)$, $Y_{\mathrm{post}}(1)$), with observed outcomes $Y_t = Y_t(1)$ on $G$ and $Y_t(0)$ off $G$, and assume no anticipation: $Y_{\mathrm{pre}}(1) = Y_{\mathrm{pre}}(0)$ almost everywhere on $G$. Write $\mathrm{DiD}(A, B) = \langle B - A\rangle_G - \langle B - A\rangle_{G^c}$ and $\tau = \langle Y_{\mathrm{post}}(1) - Y_{\mathrm{post}}(0)\rangle_G$. Then

$$\mathrm{DiD}(Y_{\mathrm{pre}}, Y_{\mathrm{post}}) = \tau + \mathrm{DiD}\big(Y_{\mathrm{pre}}(0), Y_{\mathrm{post}}(0)\big):$$

the difference in differences of observed outcomes is the post-period effect on the treated plus the parallel-trends gap of the untreated potential outcomes.
