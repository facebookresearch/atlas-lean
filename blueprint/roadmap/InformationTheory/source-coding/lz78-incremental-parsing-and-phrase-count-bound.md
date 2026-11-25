# LZ78 incremental parsing and phrase-count bound

This node collects the Lempel–Ziv 1978 parsing and its code-length bound over an alphabet $\mathcal{A}$ with
$\lvert \mathcal{A} \rvert \ge 2$.

## Expansion

A sound expansion has separate pages for:

1. **Parsing.** The parser splits $x^n$ into phrases, each equal to an earlier phrase (or the empty phrase) extended by
   one symbol; all phrases are distinct except possibly the last, which may repeat an earlier phrase when the input
   ends, and the end-of-input convention is stated.
2. **Coding.** Encoding each phrase as the index of its prefix phrase and its last symbol is a computable injective map
   whose inverse decodes the input.
3. **Phrase count.** The number $c(n)$ of phrases satisfies $c(n) \le n / ((1 - \varepsilon_n)\log_{\lvert \mathcal{A} \rvert} n)$ for
   $n \ge 2$ and a sequence $\varepsilon_n \to 0$ that does not depend on the input, and the code length is less than
   $c(n)(\log_2 c(n) + \log_2 \lvert \mathcal{A} \rvert + 1)$ bits.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Computable encoder/decoder contract.

## Sources

- J. Ziv and A. Lempel, Compression of individual sequences via variable-rate coding, IEEE Trans. Inform. Theory 24(5)
  (1978), 530–536: Section II, inequality (6) (the phrase-count bound, from Lempel and Ziv 1976, Theorem 2), and the proof
  of Theorem 2 (incremental parsing (12), its coding, and the bound $L < (p + 1)(\log (p + 1) + \log (2\alpha))$).
  <http://pzs.dstu.dp.ua/ComputerGraphics/ic/bibl/ziv_lempel_1978.pdf>
