# Regret against a fixed strategy

The regret of player $i$ against the fixed strategy $a$ over the rounds $s^1, \dots, s^T$ is

$$\sum_{t=1}^T c_i(s^t) - \sum_{t=1}^T c_i(a, s^t_{-i}),$$

how much better $i$ would have done by playing $a$ in every round while the others played as they
did. A no-regret algorithm keeps the maximum over $a$ of this quantity in $o(T)$ against every
sequence of opponents' play.

## Background

- [Hedge algorithm](../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/README.md): background, a no-regret algorithm; its loss bound makes the
  average regret $O(\sqrt{\log n / T})$ with $n$ strategies.

## Sources

- T. Roughgarden, CS364A *Algorithmic Game Theory*, Lecture #17 "No-regret dynamics", Stanford University, 2013.
