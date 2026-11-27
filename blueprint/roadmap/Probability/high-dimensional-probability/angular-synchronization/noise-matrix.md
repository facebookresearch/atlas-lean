# Hermitian noise matrix for angular synchronization

For $\omega : \{0,\dots,n-1\}^2 \times \{0,1\} \to \mathbb{R}$, the noise matrix $W$ is the $n \times n$ complex matrix with

$$W_{kl} = \omega(k, l, 0) + i\,\omega(k, l, 1) \ (k < l), \qquad W_{lk} = \overline{W_{kl}} \ (k < l), \qquad W_{kk} = 0.$$

It is Hermitian; under the noise distribution (independent $N(0, 1/2)$ coordinates) its entries $W_{kl}$, $k < l$, are independent standard complex Gaussians.
