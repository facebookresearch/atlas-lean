# Gill’s representation of the Kaplan–Meier estimator in continuous time

For one subject with failure time $T$ and censoring time $C$, observed time $X = T \wedge C > 0$, let $\hat S(t) = 1 - N(t)$ be the one-subject Kaplan–Meier estimator, $S$ a survival function and $\Lambda$ a hazard measure with $1/S(b) - 1/S(a) = \int_{(a,b]}d\Lambda/S$ for $0 \le a \le b \le t$ and $S(0) = 1$, and $R(t) = \int_{(0,t]}\hat S(s-)/S(s)\mathbf 1\{Y(s) = 0\}\,d\Lambda(s)$. Then $\hat S(t)/S(t) - 1 = -\int_{(0,t]}H\,d(N - A) + R(t)$, with $H = \hat S(s-)/(SY)$ and $A = \int Y\,d\Lambda$.
