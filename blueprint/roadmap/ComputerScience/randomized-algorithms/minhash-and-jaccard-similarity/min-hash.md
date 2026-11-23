# Min-hash of a set under a permutation

Let $U$ be a linearly ordered set, $\pi$ a permutation of $U$ and $A$ a finite subset of $U$. The min-hash of $A$ under $\pi$ is

$$h_\pi(A) = \min \pi(A) = \min_{a \in A} \pi(a) \in U \cup \{\top\},$$

the least element of the image $\pi(A)$, where $\top$ is a new element above every element of $U$ and $h_\pi(\emptyset) = \top$.
