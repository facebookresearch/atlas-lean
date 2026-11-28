# Grouped-query and multi-query attention

Let $H$ query heads of equal key width be partitioned into $G$ equal groups, $1\le G\le H$ with $G\mid H$. In grouped-query attention (GQA), head $h$ keeps its own query projection but uses the key and value projections of its group $g(h)$. Its logits are $Q_h K_{g(h)}^{\mathsf T}/\sqrt{d_k}$, masked and normalized per row; its weights multiply $V_{g(h)}$. The head outputs are concatenated and projected as usual.

$G=1$ gives multi-query attention (MQA), and $G=H$ recovers ordinary multi-head attention with independent projections. Sharing reduces the number of stored key/value heads, not the number of queries. Replacing independently trained heads by shared ones need not preserve their outputs.

## Depends on

- [Masked multi-head attention](masked-multi-head-attention.md)

## Sources

- Ainslie et al., [*GQA: Training Generalized Multi-Query Transformer Models from Multi-Head Checkpoints*](https://aclanthology.org/2023.emnlp-main.298/) (EMNLP 2023), §2.2 and figure 2.
- Shazeer, [*Fast Transformer Decoding: One Write-Head is All You Need*](https://arxiv.org/abs/1911.02150) (2019), §3, for the single-KV-head case.
