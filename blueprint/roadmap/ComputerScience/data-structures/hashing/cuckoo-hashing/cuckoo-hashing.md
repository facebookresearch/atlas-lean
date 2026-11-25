# Cuckoo hash table

Given a type $K$ of keys, a type $V$ of values, a number $m$ of slots,
and two hash functions $h_1, h_2 : K \to \{0, \dots, m - 1\}$, a cuckoo hash table consists of
two tables, each a vector of $m$ slots; every slot is either empty or holds a key–value pair
$(k, v)$ with $k \in K$ and $v \in V$. The structure itself does not require a pair $(k, v)$ to
sit at slot $h_1(k)$ of the first table or at slot $h_2(k)$ of the second.

No expected constant-time bound is claimed because the model supplies neither a probability
distribution nor an independence assumption about the hashes.
