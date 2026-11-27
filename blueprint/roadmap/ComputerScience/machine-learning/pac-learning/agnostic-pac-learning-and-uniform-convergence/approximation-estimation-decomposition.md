# Approximation-estimation (bias-complexity) decomposition

Fix a nonempty hypothesis class $H$, a loss and a distribution $D$, and let $L_D$ be the true risk. The
approximation error of $H$ is $\varepsilon_{\mathrm{app}} = \inf_{h \in H} L_D(h)$, which does not depend on
the sample. For a learner's output $h_S \in H$, the estimation error is
$\varepsilon_{\mathrm{est}} = L_D(h_S) - \varepsilon_{\mathrm{app}} \ge 0$, so that
$L_D(h_S) = \varepsilon_{\mathrm{app}} + \varepsilon_{\mathrm{est}}$. The infimum need not be attained; when it
is, it is a minimum. Enlarging $H$ can only decrease $\varepsilon_{\mathrm{app}}$ (a separate remark); the
no-free-lunch theorem is a separate result and is not part of this definition.

## Depends on

- [Expected risk](../../generalization-bounds-and-concentration/risk.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Section 5.2 (error decomposition into approximation and estimation errors). <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
