# Lamport signing

The signature of a message $m \in \{0, 1\}^\ell$ under a secret key
$sk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to X$ is $\sigma \in X^\ell$ with
$\sigma_i = sk(i, m_i)$ for every position $i < \ell$.
