# Identification of the ATT by 2×2 difference-in-differences

Let $G$ be a measurable treated group in a measure space, with potential outcomes $Y_{\mathrm{pre}}(0), Y_{\mathrm{pre}}(1), Y_{\mathrm{post}}(0), Y_{\mathrm{post}}(1)$, where $Y_{\mathrm{pre}}(0)$, $Y_{\mathrm{post}}(0)$ and $Y_{\mathrm{post}}(1)$ are integrable on $G$. Observed outcomes are $Y(1)$ on $G$ and $Y(0)$ off $G$. Assume no anticipation, $Y_{\mathrm{pre}}(1) = Y_{\mathrm{pre}}(0)$ almost everywhere on $G$, and parallel trends, $\operatorname{avg}_G\bigl(Y_{\mathrm{post}}(0) - Y_{\mathrm{pre}}(0)\bigr) = \operatorname{avg}_{G^c}\bigl(Y_{\mathrm{post}}(0) - Y_{\mathrm{pre}}(0)\bigr)$, where $\operatorname{avg}_A$ is the set average over $A$. Then the difference in differences of observed outcomes,

$$\operatorname{avg}_G(Y_{\mathrm{post}} - Y_{\mathrm{pre}}) - \operatorname{avg}_{G^c}(Y_{\mathrm{post}} - Y_{\mathrm{pre}}),$$

equals the post-period effect on the treated, $\operatorname{avg}_G\bigl(Y_{\mathrm{post}}(1) - Y_{\mathrm{post}}(0)\bigr)$.
