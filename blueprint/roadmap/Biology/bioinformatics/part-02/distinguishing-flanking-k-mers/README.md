# Distinguishing flanking k-mers

$k$-mer pseudoalignment against a transcriptome mismaps reads that come from intronic or intergenic sequence but share long substrings with transcripts. Adding to the index only the genome $k$-mers that flank such shared sequences, left uncoloured so that any read containing one is discarded, filters external reads at a memory cost bounded by the index size, and with an index of both nascent and mature transcripts lets reads be classified as nascent, mature or ambiguous.

- [Distinguishing flanking k-mers and their space bound](distinguishing-flanking-k-mers-and-their-space-bound.md)
