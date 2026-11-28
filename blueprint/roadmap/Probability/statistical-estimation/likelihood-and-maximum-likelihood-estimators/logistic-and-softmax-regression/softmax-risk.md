# Empirical risk of softmax regression

For data $(X_k, Y_k)_{k < m}$ with features $X_k \in \mathbb{R}^\iota$, for a finite index set $\iota$, and labels $Y_k$ in a finite nonempty set $C$ of classes, and class weights $W_c \in \mathbb{R}^\iota$ for $c \in C$, the empirical risk of softmax regression is the total cross-entropy of the $m$ observations, with no division by $m$:

$$R(W) = \sum_{k < m} \Bigl[\log\Bigl(\sum_{c \in C} \exp(W_c \cdot X_k)\Bigr) - W_{Y_k} \cdot X_k\Bigr].$$
