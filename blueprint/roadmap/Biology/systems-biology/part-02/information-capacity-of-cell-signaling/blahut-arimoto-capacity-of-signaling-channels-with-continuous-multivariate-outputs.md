# Blahut–Arimoto capacity of signaling channels with continuous multivariate outputs

**Setting.** The input $X$ takes values $x_1, \dots, x_m$ (stimulus doses), and given $X = x_i$ the single-cell response $Y \in \mathbb R^d$ has density $P(y \mid x_i)$. For an input distribution $P(X)$ the mutual information (in nats) is

$$I(X; Y) = \sum_{i=1}^{m} P(x_i) \int_{\mathbb R^d} P(y \mid x_i) \ln \frac{P(x_i \mid y)}{P(x_i)}\, dy,$$

and the channel capacity is $C^* = \max_{P(X)} I(X; Y)$; $e^{C^*}$ is interpreted as the number of input levels the cell can distinguish.

**Double maximization.** For a conditional distribution $Q(X \mid Y)$ (for each $y$ a probability vector on $\{x_1, \dots, x_m\}$) define

$$J\bigl(P, Q\bigr) = \sum_{i=1}^{m} P(x_i) \int_{\mathbb R^d} P(y \mid x_i) \ln \frac{Q(x_i \mid y)}{P(x_i)}\, dy .$$

Then $C^* = \max_{P} \max_{Q} J(P, Q)$, and each partial maximum is explicit:

- for fixed $P$, $J$ is maximized by the posterior $Q^*(x_i \mid y) = P(x_i) P(y \mid x_i) / \sum_{r} P(x_r) P(y \mid x_r)$, where $J(P, Q^*) = I(X; Y)$;
- for fixed $Q$, $J$ is maximized by

    $$P^*(x_i) = \frac{e^{D_i(Q)}}{\sum_{r=1}^{m} e^{D_r(Q)}}, \qquad D_i(Q) = \int_{\mathbb R^d} P(y \mid x_i) \ln Q(x_i \mid y)\, dy .$$

**Algorithm and convergence.** Alternate $Q^{(k)} = Q^*(\,\cdot\,; P^{(k)})$ and $P^{(k+1)} = P^*(\,\cdot\,; Q^{(k)})$, with capacity estimate $C^{(k)} = \sum_i P^{(k)}(x_i)\bigl(D_i(Q^{(k)}) - \ln P^{(k)}(x_i)\bigr)$. Then $P^{(k)} \to P^*$ and $C^{(k)} \to C^*$. In practice $D_i$ is estimated by averaging $\ln Q(x_i \mid y)$ over cells measured at dose $x_i$, and $Q$ by a multinomial logistic regression of the dose on the response vector; when $P(X)$ changes from $P^{(k-1)}$ to $P^{(k)}$ only the intercepts change,

$$\alpha_i^{(k)} = \alpha_i^{(k-1)} + \ln\frac{P^{(k-1)}(x_m)}{P^{(k-1)}(x_i)} - \ln\frac{P^{(k)}(x_m)}{P^{(k)}(x_i)},$$

so the classifier is fitted only once.

## Expansion

For fixed $P$, $J(P, Q^*) - J(P, Q) = \int P(y) \, \mathrm{KL}\bigl(Q^*(\cdot \mid y) \,\|\, Q(\cdot \mid y)\bigr)\, dy \ge 0$, which gives the posterior as maximizer and identifies the maximum with the mutual information; hence the double maximum equals the capacity. For fixed $Q$, $J = \sum_i P(x_i)(D_i - \ln P(x_i))$ is a concave function on the simplex, and a Lagrange multiplier for $\sum_i P(x_i) = 1$ yields the softmax of the $D_i$. Monotone increase of $J$ along the alternation and Arimoto's convergence argument carry over from discrete to continuous outputs. The intercept update holds because changing the prior multiplies posterior odds $Q(x_i \mid y)/Q(x_m \mid y)$ by the ratio of prior odds while leaving the likelihood ratio, captured by the slope coefficients, unchanged. Classifier-based estimation avoids density estimation in high dimension, which is what makes the method usable on multivariate single-cell measurements.

## Sources

- T. Jetka, K. Nienałtowski, T. Winarski, S. Błoński, M. Komorowski, "Information-theoretic analysis of multivariate single-cell signaling responses", PLoS Computational Biology (2019), Methods, capacity definition (Eqs. 3–4), double maximization (Eqs. 11–12; Lemma 1 in S1 Text), explicit maximizers (Eqs. 13–17; Lemma 2), alternating maximization and convergence (Eqs. 18–21; Lemma 4), logistic-regression estimation and intercept update (Eqs. 10, 26; Lemma 6), and Box 1. <https://doi.org/10.1371/journal.pcbi.1007132> (PMC6655862).
