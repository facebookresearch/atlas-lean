# Collision probability under a uniform key

Let `H` be a keyed hash function
with finite key type $K$, and let $x$ and $y$ be inputs. If $K$ is nonempty, the
probability that the hashes of $x$ and $y$ agree under a uniform key is
$|\{k \in K : H(k,x) = H(k,y)\}|/|K|$. Each key counts separately even if two
keys induce the same function. On the empty key type the ratio returns zero by
convention; it does not describe a uniform distribution there.
