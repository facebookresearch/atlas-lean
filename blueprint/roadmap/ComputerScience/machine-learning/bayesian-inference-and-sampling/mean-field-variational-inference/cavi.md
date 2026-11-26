# Mean-field (CAVI) update of the first factor

Let $A$ and $B$ be finite sets, let
$p : A \times B \to \mathbb{R}$ be a joint and let $q_2 : B \to \mathbb{R}$. The
coordinate-ascent update of the first factor is the function $q_1 : A \to \mathbb{R}$ given by

$$q_1(a) = \frac{\exp E(a)}{\sum_{a' \in A} \exp E(a')},$$

where $E(a) = \sum_{b \in B} q_2(b) \log p(a, b)$ is the expected log-joint of $a$ under $q_2$.
That is, $q_1(a) \propto \exp \mathbb{E}_{q_2}[\log p(a, \cdot)]$.

Here $\log$ is the real logarithm extended by $\log x = \log |x|$ for $x < 0$ and $\log 0 = 0$.
