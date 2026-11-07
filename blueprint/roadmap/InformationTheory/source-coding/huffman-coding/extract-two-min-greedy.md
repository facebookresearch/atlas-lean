# Two-minimum extraction is greedy

Order Huffman priorities lexicographically by weight and
then serial number. If extracting two minima from a binary min-heap $h$ of Huffman priorities
succeeds with first priority $p_1$, second priority $p_2$ and remaining heap $h'$, then
$p_1 \le q$ for every element $q$ of $h$, and $p_2 \le q$ for every $q$ that is $p_2$ or an
element of $h'$.
