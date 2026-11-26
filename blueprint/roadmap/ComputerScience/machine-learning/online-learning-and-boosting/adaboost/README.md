# AdaBoost

- [Weighted training error](err.md)
- [AdaBoost's hypothesis weight](alpha.md)
- [Normalizer of a boosting round](normalizer.md)
- [AdaBoost reweighting](reweight.md)
- [AdaBoost's reweighting is a normalized Hedge step](reweight-eq-hedge-update.md)
- [The normalizer of a round is $2\sqrt{\varepsilon(1 - \varepsilon)}$](normalizer-eq.md)
- [One round's factor is at most $e^{-2\gamma^2}$ under a uniform edge](two-mul-sqrt-le-exp.md)
- [AdaBoost's weights](dist.md)
- [Weak hypothesis of an AdaBoost round](hyp.md)
- [Weighted error of an AdaBoost round](eps.md)
- [Normalizer of an AdaBoost round](zee.md)
- [AdaBoost's combined score](score.md)
- [Training error of AdaBoost](train-err.md)
- [Unrolling the weights](dist-mul-prod.md)
- [The training error is at most the product of the normalizers](train-err-le-prod.md)
- [The weak-learning assumption](weak-learner.md)
- [The Freund–Schapire bound on AdaBoost's training error](train-err-le-prod-sqrt.md)
- [AdaBoost drives the training error down exponentially](train-err-le-exp.md)
- [Freund and Schapire's training-error bound with per-round errors](train-err-le-prod-sqrt-of-eps.md)
- [AdaBoost training error is at most the exponential of the round errors](train-err-le-exp-of-round-errors.md)
- [A round's factor in terms of its edge](two-mul-sqrt-eq-sqrt-one-sub.md)
- [A round's factor is at most $e^{-2\gamma^2}$ for its own edge](two-mul-sqrt-le-exp-edge.md)
- [AdaBoost's training error in terms of the edges](train-err-le-exp-sum-sq.md)
- [The exponential loss](exp-loss.md)
- [The exponential loss after $T$ rounds is the product of the normalizers](exp-loss-score.md)
- [The reweighted mass along a hypothesis](sum-mul-exp-eq.md)
- [The exponential loss along a coordinate](exp-loss-score-add.md)
- [No step along any hypothesis beats the factor $2\sqrt{\varepsilon(1-\varepsilon)}$](exp-loss-score-mul-le-exp-loss-add.md)
- [One AdaBoost round multiplies the exponential loss by $2\sqrt{\varepsilon_T(1-\varepsilon_T)}$](exp-loss-score-succ.md)
- [AdaBoost is greedy coordinate descent on the exponential loss](exp-loss-score-succ-le.md)
- [The training margin error](margin-err.md)
- [AdaBoost's training margins](margin-err-le.md)

## Related topics

- [PAC learning](../../pac-learning/README.md): boosting was introduced to answer Kearns and
  Valiant's question whether weak learnability, accuracy slightly better than random guessing,
  implies PAC learnability; the training-error bound here is the empirical side of that answer.
- [Hedge algorithm](../hedge-algorithm/README.md): AdaBoost is Hedge run on the training points, with
  the step size chosen per round; Freund and Schapire derive its training-error bound from Hedge's
  weight-decay argument.
- [Boosting and the minimax theorem](../boosting-and-the-minimax-theorem/README.md): why a weak learner
  on every distribution makes the target a weighted majority vote, the object AdaBoost approximates.
- [Rademacher complexity](../../generalization-bounds-and-concentration/rademacher-complexity/README.md):
  the margin costs of voting classifiers, the generalization side of the training-margin bound here.
