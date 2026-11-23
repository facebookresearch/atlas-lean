# Ordinary kriging

Ordinary kriging is unbiased: the kriging weights solve the ordinary
kriging system, whose last equation is the unbiasedness constraint that the
weights sum to `1`. If every observation has the same mean `mean`, the
kriging estimator `∑ i, lam i * Z i` has mean `mean`. The covariance
equations pin down which weights solve the system; unbiasedness itself
follows from the constraint.
