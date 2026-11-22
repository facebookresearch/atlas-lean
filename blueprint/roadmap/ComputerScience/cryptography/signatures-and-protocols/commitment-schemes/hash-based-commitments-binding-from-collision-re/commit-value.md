# Hash commitment value

For a keyed hash $H$ on pairs of a nonce and a message, the commitment value of a message $m$ with
nonce $r$ under the key $s$ is $H_s(r, m)$. The pair models the concatenation $r \| m$ for a
fixed-length nonce.
