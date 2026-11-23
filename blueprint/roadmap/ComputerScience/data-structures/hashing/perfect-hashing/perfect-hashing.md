# Two-level perfect hash table

Fix a type $\alpha$ of keys, a type $\beta$ of values and a
primary hash function $h : \alpha \to \mathbb{N}$. A two-level (FKS) perfect hash table consists
of a number $b > 0$ of buckets and, for each bucket $i < b$, a secondary size $m_i \in \mathbb{N}$,
a secondary hash function $h_i : \alpha \to \mathbb{N}$ and a secondary table of $m_i$ slots, each
of which is empty or holds one binding $(k, v)$ with $k \in \alpha$ and $v \in \beta$.

The intended position of a key $k$ is slot $h_i(k) \bmod m_i$ of bucket $i = h(k) \bmod b$. The
structure itself imposes no condition on the hash functions and does not require bindings to sit
at their intended positions; that requirement is the separate validity condition.
