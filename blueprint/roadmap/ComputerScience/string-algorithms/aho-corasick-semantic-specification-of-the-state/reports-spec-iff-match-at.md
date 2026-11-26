# Reports Spec iff match At

The specified reports in the shared string-matching semantics: a nonempty pattern `p` is
reported ending at position `i` iff it fits before `i + 1` and matches at the offset
`i + 1 - p.length` in the sense of `MatchAt`.
