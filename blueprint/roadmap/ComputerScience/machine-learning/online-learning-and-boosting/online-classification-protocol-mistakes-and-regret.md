# Online classification protocol, mistakes and regret

In online binary classification over rounds $t = 1, \dots, T$, the environment reveals $x_t$, the learner outputs a
prediction, and then $y_t \in \{0,1\}$ is revealed. The learner computes its prediction in round $t$ from the earlier
examples $(x_1, y_1), \dots, (x_{t-1}, y_{t-1})$ and the instance $x_t$. A deterministic learner outputs
$\hat y_t \in \{0,1\}$ and its number of mistakes is $\sum_t \mathbf{1}[\hat y_t \ne y_t]$
([mistakes of a deterministic online learner](mistakes.md)). A randomized learner outputs $p_t \in [0,1]$ and then
predicts $\hat y_t \sim \mathrm{Bernoulli}(p_t)$ with fresh randomness; its expected number of mistakes is
$\sum_t \lvert p_t - y_t \rvert$
([expected mistakes of a randomized online learner](integral-mistakes-eq-expected-mistakes.md)), also the loss of the
fractional prediction $p_t$ under absolute loss, whereas $\sum_t \mathbf{1}[p_t \ne y_t]$ is not: it is at least
$\sum_t \lvert p_t - y_t \rvert$, and larger as soon as some $p_t$ lies strictly between $0$ and $1$. The regret against
a class $H$ of hypotheses $h : X \to \{0,1\}$ is
$\sum_t \lvert p_t - y_t \rvert - \min_{h \in H} \sum_t \lvert h(x_t) - y_t \rvert$, where
$\sum_t \lvert h(x_t) - y_t \rvert$ is the number of mistakes of $h$, seen as the learner that predicts $h(x_t)$. The
minimum exists, as these numbers are natural numbers, and is taken to be $0$ when $H$ is empty. The realizable setting
requires some $h \in H$ consistent with every $(x_t, y_t)$; the minimum is then $0$, and the regret is the expected
number of mistakes.

The environment is adaptive (choosing $x_t, y_t$ after seeing past predictions) for deterministic learners and
oblivious (fixing the sequence in advance) for randomized learners, unless stated otherwise. A deterministic learner's
predictions are functions of the earlier examples, so an adaptive environment produces a single sequence against it,
and a statement about every sequence covers adaptive environments. The expected number of mistakes of a randomized
learner is taken over its predictions on a fixed sequence.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Chapter 21: the online classification protocol, the realizable case and mistake bounds (Section 21.1, Definition 21.1), and the unrealizable case (Section 21.2), with predictions $p_t \in [0,1]$ read as the probability of predicting $1$, so that $\mathbb{P}[\hat y_t \ne y_t] = \lvert p_t - y_t \rvert$, and the regret, equations (21.1) and (21.2), which also take the supremum over sequences of length $T$. Section 21.2 lets the environment see the learner's random predictions of the earlier rounds, though not that of the current round. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
