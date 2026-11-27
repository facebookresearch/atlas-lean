# Exact uniform resampling of random tables on the Word RAM

On a randomized Word RAM, whose `rand` instruction returns a uniform value below a bound $m$ given in a register (so $1 \le m < 2^w$), a loop that fills $N$ table entries with independent `rand` draws below $2^M$ ($M < w$) produces, as the distribution of the table contents, exactly the uniform distribution on $[2^M]^N$; when the entries are $b$-bit fields packed in words, filling the packed array word by word with uniform $w$-bit words gives the uniform distribution on $[2^b]^N$, where for $w \ge 2$ each uniform word is $2^{w-1}\,\mathrm{rand}(2) + \mathrm{rand}(2^{w-1})$, two draws whose bounds fit in a word ($2^w$ itself does not). The loop runs in $O(N)$ instructions.

## Proof sketch

The loop's output is a product of independent uniform draws, one per entry (a word assembled from independent uniform draws below $2$ and below $2^{w-1}$ is uniform on $[2^w]$), and reading the fields of a packed array selects disjoint sets of bit positions of uniformly random words, so the fields are independent and uniform (bits outside every field are ignored).

## Depends on

- [Word-RAM resamplable hash family](word-ram-resamplable-hash-family.md)
- [Bit-packed array on the Word RAM](bit-packed-array.md)
- [Randomized word RAM](../../../../sorting-and-searching/word-ram-integer-algorithms/randomized-word-ram.md)

## Sources

- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
- M. Mitzenmacher and E. Upfal, "Probability and Computing", 2nd edition, Cambridge University Press, 2017.
