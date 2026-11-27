# AdaBoost's combined score

After $T$ rounds, the combined score of training point $i$ is

$$F_T(i) = \sum_{t < T} \alpha(\varepsilon_t)\, h_t(i),$$

where $\varepsilon_t$ is the weighted error and $h_t$ the weak hypothesis of round $t$,
$\alpha(\varepsilon) = \frac{1}{2} \log \frac{1 - \varepsilon}{\varepsilon}$ is the hypothesis
weight, and the prediction $h_t(i)$ is read as $\pm 1$. The final classifier is the sign of
$F_T$.
