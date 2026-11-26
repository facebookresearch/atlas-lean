# Random-walk insertion for d-ary cuckoo hashing

*Random-walk insertion* (Fotakis, Pagh, Sanders and Spirakis) inserts a new key $x_1$ as follows: if one of the slots $h_1(x_1), \dots, h_d(x_1)$ is empty, place $x_1$ there; otherwise choose $i_1 \in [d]$ uniformly at random, place $x_1$ in $h_{i_1}(x_1)$, evict the key $x_2$ held there and reinsert $x_2$ by the same rule with a fresh uniform index $i_2 \in [d]$, and so on until a key is placed into an empty slot. The *insertion time* is the number of placements performed.

## Depends on

- [d-ary cuckoo hashing and its hashing graph](d-ary-cuckoo-hashing.md)

## Sources

- Dimitris Fotakis, Rasmus Pagh, Peter Sanders, Paul Spirakis, "Space Efficient Hash Tables with Worst Case Constant Access Time", Theory of Computing Systems 38(2) (2005).
- Tolson Bell, Alan Frieze, "O(1) Insertion for Random Walk d-ary Cuckoo Hashing up to the Load Threshold", FOCS (2024), arXiv:2401.14394.
