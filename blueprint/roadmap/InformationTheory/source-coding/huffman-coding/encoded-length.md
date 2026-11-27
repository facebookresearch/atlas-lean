# Encoded length of a coding tree

The encoded length of a leaf of weight $w$ is $w$ (its
lone symbol receives a one-bit codeword). The encoded length of the tree with left subtree $L$
and right subtree $R$ is $P(L) + P(R) + W(L) + W(R)$, where $P$ is the weighted path length and
$W$ the total weight; this is the weighted path length of that tree.

When the leaf symbols are distinct, the encoded length equals the encoder's emitted cost, the
sum over the weighted leaves of weight times codeword length. When symbols repeat, the encoder
resolves each symbol to its first leaf, so on such trees the encoded length is the structural
path cost rather than the emitted cost.
