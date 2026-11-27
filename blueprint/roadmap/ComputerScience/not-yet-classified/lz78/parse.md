# LZ78 incremental parsing

The LZ78 parse of a finite list $x$ is the list of phrases that
`LZ78.parseEncodeAux [] x (|x| + 1)` returns. Each phrase is the shortest nonempty prefix of the
unparsed input that is not an earlier phrase; if every nonempty prefix of the unparsed input is
an earlier phrase, the unparsed input is the last phrase.
