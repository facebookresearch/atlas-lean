# Approximate circular string matching

Circular string matching asks for every factor of a text that equals some rotation of a pattern, exactly or within $k$ mismatches. It arises when searching circular genomes (bacterial, mitochondrial, viral) where the linear sequence start is arbitrary. Filtering algorithms split the doubled pattern into fragments so that, by a pigeonhole argument, every rotation contains enough exact fragment occurrences to anchor a cheap verification.

- [Fragment filtering for approximate circular string matching](fragment-filtering-for-approximate-circular-string-matching.md)
