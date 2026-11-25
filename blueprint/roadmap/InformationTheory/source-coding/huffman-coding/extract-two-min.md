# Extracting two minima from a Huffman heap

Given a binary min-heap $h$ of Huffman
priorities, extract the minimum of $h$, obtaining a priority $p_1$ and a heap $h_1$, then extract
the minimum of $h_1$, obtaining a priority $p_2$ and a heap $h_2$. The result is the triple
$(p_1, p_2, h_2)$; if either extraction meets an empty heap, there is no result.
