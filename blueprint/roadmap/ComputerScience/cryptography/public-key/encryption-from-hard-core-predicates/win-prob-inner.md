# The predictor's success for one key and one coin

Fix the key, the distinguisher's coins and the permutation. With a fair bit $c$ and a uniform $x$, the
[predictor built from $A$](predictor.md) outputs $b(x)$ with probability
$\tfrac12 + \tfrac12 \bigl(\Pr_x[A(p(x), b(x)) = 1] - \Pr_x[A(p(x), \lnot b(x)) = 1]\bigr)$. For each $x$
it is right when $c = b(x)$ and $A$ accepts, or when $c \ne b(x)$ and $A$ rejects.
