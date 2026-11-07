# Gelfond–Schneider theorem for every value of a complex power

Let $a, b \in \mathbb{C}$
be algebraic over $\mathbb{Q}$ with $a \neq 1$ and $b \notin \mathbb{Q}$, and let $z \in \mathbb{C}$
satisfy $e^z = a$. Then $e^{bz}$ is transcendental over $\mathbb{Q}$.

The hypothesis $e^z = a$ already implies $a \neq 0$. Taking $z = \log a + 2 \pi i n$, where
$\log a$ is the principal logarithm and $n$ is an integer, recovers every branch of $a^b$.

## Sources

- A. O. Gelfond, *Sur le septième problème de Hilbert* (1934), and T. Schneider, *Transzendenzuntersuchungen periodischer Funktionen I. Transzendenz von Potenzen*, J. Reine Angew. Math. 172 (1935), 65–69, DOI 10.1515/crll.1935.172.65. Explicit arbitrary- and principal-branch applications occur in arXiv:2311.11127v1, arXiv:2607.23662v1, and arXiv:2608.17545v1. The Lean formalization in arXiv:2603.24823v1 states only the principal `Complex.cpow` value; this declaration records the arbitrary-logarithm form.
