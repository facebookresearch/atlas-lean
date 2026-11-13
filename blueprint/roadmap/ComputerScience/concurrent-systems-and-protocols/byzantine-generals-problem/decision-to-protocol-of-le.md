# `toProtocol` runs `OM(m)`

After any number `r ≥ m + 1` of rounds of `toProtocol c m`
with commander `c`, order `v`, traitors `traitors` and traitor messages `adv`, every general `p`
decides the value of `om` in which the loyal generals are those outside `traitors` and the
traitors relay `advOfMessages adv`. Rounds after the first `m + 1` write only the entries for
paths longer than `m + 1`, which the decision does not read.
