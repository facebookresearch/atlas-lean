# Polynomial Commitment Relative Batch

Class-relative security for the **pre-commitment batch** experiment. At parameter `κ`,
setup at bound `t κ` supplies the prime as part of the public key. Each binding conflict must
have negligible probability for every family in its supplied report class. In computational
mode every family in a third supplied class must have negligible absolute fresh-prediction
success; in unconditional mode the full view must give exactly no extra information beyond the
public evaluations. These arbitrary classes are not a definition of PPT. Empty classes impose
no computational tests; nonempty classes need not include all uniform PPT rules. In computational
mode, if the predictor class includes an independent uniform guess at an always-fresh index,
the setup average of `1 / p` must be negligible. Unconditional hiding imposes no such bound on
absolute prediction success.
