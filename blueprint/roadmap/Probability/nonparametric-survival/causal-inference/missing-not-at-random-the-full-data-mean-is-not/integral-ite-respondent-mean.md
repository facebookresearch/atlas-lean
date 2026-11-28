# Mean imputation estimates the respondents' mean

Let $P$ be a probability measure on $\{0,1\} \times \mathbb R$ (points $(r, y)$, $r = 1$ for response) with $y$ integrable and $P(r = 1) \ne 0$, and let $m(P) = \frac{\int_{\{r = 1\}} y \, dP(r, y)}{P(r = 1)}$ be the respondents' mean. Filling every missing outcome with $m(P)$ gives a completed outcome whose mean is $m(P)$ itself:

$$\int \bigl(\mathbf 1[r = 1]\, y + \mathbf 1[r = 0]\, m(P)\bigr) \, dP(r, y) = m(P).$$
