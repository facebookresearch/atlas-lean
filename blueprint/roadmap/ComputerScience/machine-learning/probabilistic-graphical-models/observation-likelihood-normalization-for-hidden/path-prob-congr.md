# Path weight depends only on the observed prefix

Let $h$ be a hidden Markov model with real weights and let $x, x' : \mathbb{N} \to O$ be observation streams. For every $t \in \mathbb{N}$ such that $x_i = x'_i$ for all $i \le t$, and every state path $z = (z_0, \dots, z_t)$, the joint weight of $z$ with $x_0, \dots, x_t$ equals the joint weight of $z$ with $x'_0, \dots, x'_t$.
