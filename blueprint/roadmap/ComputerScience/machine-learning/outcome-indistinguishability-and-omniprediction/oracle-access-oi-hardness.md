# Oracle- and code-access outcome indistinguishability is computationally hard

Under fine-grained average-case hardness assumptions (as used for average-case fine-grained complexity), there are distributions and distinguisher classes of polynomial size for which no predictor of substantially smaller complexity than the distinguishers is oracle-access outcome indistinguishable, whereas sample-access OI predictors of comparable size exist. Thus the levels of the OI hierarchy separate computationally: allowing auditors query access to a predictor makes indistinguishability strictly harder to achieve than allowing them only to see historical predictions.

## Proof sketch

Embed a fine-grained hard problem into the outcome distribution so that oracle access to $p$ allows the distinguisher to evaluate $p$ on correlated inputs and check a consistency relation that Nature's outcomes satisfy; any predictor passing the check would solve the embedded problem faster than the assumed lower bound, while weaker access levels cannot exercise this relation.

## Depends on

- [Outcome indistinguishability and its access hierarchy](outcome-indistinguishability.md)

## Proof depends on

- [Outcome indistinguishability and its access hierarchy](outcome-indistinguishability.md)

## Sources

- C. Dwork, M. P. Kim, O. Reingold, G. N. Rothblum, G. Yona, "Outcome Indistinguishability", STOC (2021), arXiv:2011.13426.
