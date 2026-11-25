# Open-addressing hash table

Let $K$ be a type of keys, $V$ a type of values, $m$ a natural
number, and $p$ a probe sequence assigning to each key $k$ and each $i \in \mathbb{N}$ a slot
$p(k, i) \in \{0, \dots, m - 1\}$. An open-addressing hash table with $m$ slots and probe
sequence $p$ consists of $m$ slots, each either empty or holding a single pair $(k, v)$ with
$k \in K$ and $v \in V$.

No expected constant-time bound is claimed because the model supplies neither a probability
distribution nor a uniform-hashing assumption about the probe sequence.
