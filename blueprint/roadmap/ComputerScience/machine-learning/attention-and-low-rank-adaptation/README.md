# Attention and low-rank adaptation

Linear algebra of recent methods for adapting and running transformer layers: low-rank adaptation of a frozen weight matrix (LoRA), its initialisation from the principal singular values and vectors of the pretrained matrix (PiSSA), and the identity-plus-rank-one state transitions of delta-rule linear attention (DeltaNet). These pages are expositions of published methods; each names the linear algebra it relies on, and how, under Informally uses. The online normalizer page states the exact identity behind one-pass softmax normalization. Singular value decompositions are under [matrix decompositions](../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/README.md).

- [Low-rank adaptation (LoRA)](low-rank-adaptation.md)
- [Principal singular values and vectors adaptation (PiSSA)](principal-singular-adaptation.md)
- [Delta-rule linear attention](delta-rule-linear-attention.md)
- [Attention logits as bilinear forms](attention-logits-as-bilinear-forms.md)
- [Rotary position embedding (RoPE)](rotary-position-embedding.md)
- [Multi-head latent attention (MLA)](multi-head-latent-attention.md)
- [The online normalizer computes the softmax normalizer](online-normalizer-computes-the-softmax-normalizer.md)
