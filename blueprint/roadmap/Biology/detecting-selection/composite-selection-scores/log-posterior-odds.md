# Additivity of evidence on the log-odds scale

In every [composite-score model](composite-model.md) with prior $\pi$ and for every observation $x$,

$$\log \frac{\mathrm{Post}(x)}{1 - \mathrm{Post}(x)} = \log \frac{\pi}{1 - \pi} + \sum_{i=1}^{k} \log B_i(x_i),$$

where $\mathrm{Post}$ is the [normalized composite score](posterior.md) and $B_i$ the component [Bayes factors](bayes-factor.md).
