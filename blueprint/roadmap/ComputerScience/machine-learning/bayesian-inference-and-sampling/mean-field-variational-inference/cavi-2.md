# Mean-field (CAVI) update of the second factor

Let $A$ and $B$ be finite sets, let
$p : A \times B \to \mathbb{R}$ be a joint and let $q_1 : A \to \mathbb{R}$. The
coordinate-ascent update of the second factor is the function $q_2 : B \to \mathbb{R}$ given by

$$q_2(b) = \frac{\exp F(b)}{\sum_{b' \in B} \exp F(b')},$$

where $F(b) = \sum_{a \in A} q_1(a) \log p(a, b)$. That is,
$q_2(b) \propto \exp \mathbb{E}_{q_1}[\log p(\cdot, b)]$; it is the update of the first factor
applied to the joint with its two factors swapped.

Here $\log$ is the real logarithm extended by $\log x = \log |x|$ for $x < 0$ and $\log 0 = 0$.
