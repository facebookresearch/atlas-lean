# Online classification protocol, mistakes and regret

In online binary classification over rounds $t = 1, \dots, T$, the environment reveals $x_t$, the learner outputs a
prediction, and then $y_t \in \{0,1\}$ is revealed. A deterministic learner outputs $\hat y_t \in \{0,1\}$ and its
number of mistakes is $\sum_t \mathbf{1}[\hat y_t \ne y_t]$. A randomized learner outputs $p_t \in [0,1]$ and then
predicts $\hat y_t \sim \mathrm{Bernoulli}(p_t)$ with fresh randomness; its expected number of mistakes is
$\sum_t \lvert p_t - y_t \rvert$ (also the loss of the fractional prediction $p_t$ under absolute loss), whereas
$\sum_t \mathbf{1}[p_t \ne y_t]$ is not. The regret against a class $H$ is
$\sum_t \lvert p_t - y_t \rvert - \min_{h \in H} \sum_t \lvert h(x_t) - y_t \rvert$. The realizable setting requires
some $h \in H$ consistent with every $(x_t, y_t)$. The environment is adaptive (choosing $x_t, y_t$ after seeing past
predictions) for deterministic learners and oblivious (fixing the sequence in advance) for randomized learners,
unless stated otherwise.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Chapter 21: the online classification protocol and mistake bounds (Section 21.1) and online learnability in the unrealizable case with randomized predictions and regret (Section 21.2). <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
