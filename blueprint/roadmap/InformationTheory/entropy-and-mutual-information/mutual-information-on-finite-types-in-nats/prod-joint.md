# Prod Joint

Let $p$ be a probability mass function on $\alpha$ and $q$ a probability mass function on $\beta$. Their product (independent) joint law is the probability mass function $p \otimes q$ on $\alpha \times \beta$ obtained by drawing $a \sim p$ and then $b \sim q$ independently and returning $(a, b)$; equivalently,

$$(p \otimes q)(x, y) = \sum_{a} p(a) \, q\big(\{b : (a, b) = (x, y)\}\big).$$
