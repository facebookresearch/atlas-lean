# Lamport verification

Let $f : X \to Y$. A signature $\sigma \in X^\ell$ on a message
$m \in \{0, 1\}^\ell$ is valid for a public key $pk : \{0, \dots, \ell - 1\} \times \{0, 1\} \to Y$
when $f(\sigma_i) = pk(i, m_i)$ for every position $i < \ell$.
