# Measurement matrix of angular synchronization

For a signal $z \in \mathbb{C}^n$, a noise level $\sigma \in \mathbb{R}$ and $\omega : \{0,\dots,n-1\}^2 \times \{0,1\} \to \mathbb{R}$, the measurement matrix is the $n \times n$ complex matrix

$$C = z z^\ast + \sigma W,$$

where $W$ is the Hermitian noise matrix with $W_{kl} = \omega(k,l,0) + i\,\omega(k,l,1)$ for $k < l$, $W_{lk} = \overline{W_{kl}}$ and $W_{kk} = 0$.
