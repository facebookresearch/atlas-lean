# Kalman filter

- [Gaussian belief](belief.md)
- [Valid Gaussian beliefs](valid.md)
- [Law of a belief](law.md)
- [Kalman prediction](predict.md)
- [Kalman gain](gain.md)
- [Kalman filter update](update.md)
- [Kalman filter step](step.md)
- [Prediction preserves validity](predict-valid.md)
- [Schur form of the updated covariance](update-cov-eq.md)
- [The Kalman update preserves validity](update-valid.md)
- [A filter step preserves validity](step-valid.md)
- [The predict step is exact](map-predict.md)
- [The update step is the exact posterior](cond-distrib-update.md)
- [One filter step is the exact posterior](cond-distrib-step.md)

## Related topics

- [Gaussian conditioning](../../../../Probability/distributions/continuous/gaussian-conditioning/README.md): the Gaussian Bayes update behind each filtering step.
- [Hidden Markov models](../hidden-markov-models/README.md): the discrete-state analogue with the forward algorithm.
- [Controllability of linear systems](../../../../Analysis/control-theory/controllability-of-linear-systems/README.md): the control problem dual to estimation; observability of $(A, C)$ is the Kalman rank condition for the pair $(A^\top, C^\top)$.
- [Recursive least squares](../../../../Analysis/control-theory/recursive-least-squares/README.md): the Kalman filter for a constant state observed through a linear regression with unit noise variance.
