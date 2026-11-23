# Shrink Matrix

The shrinkage matrix `K = (h² / M) R V⁻¹` with `V = scoreCov` the covariance of the marginal
scores: `K β̂` is the best linear predictor of `β` from `β̂` when `V` is invertible. (When `V` is
singular, Mathlib's inverse is `0` and so is `K`.)
