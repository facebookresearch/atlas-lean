# Correctness of Diffie–Hellman key agreement

Let $G$ be a group, $q$ a natural number and
$g \in G$. For $x \in G$ and $c \in \mathbb{Z}/q\mathbb{Z}$ write $x^c$ for $x^n$, where $n$ is
the natural-number value of $c$: its representative in $\{0, \dots, q-1\}$ when $q > 0$, and
$|c|$ when $q = 0$ (in which case $\mathbb{Z}/q\mathbb{Z} = \mathbb{Z}$). Then
$(g^b)^a = (g^a)^b$ for all $a, b \in \mathbb{Z}/q\mathbb{Z}$.
