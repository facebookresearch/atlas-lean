# Book value under straight-line depreciation

The book value after `t` periods of straight-line depreciation over a useful
life of `life` periods is `cost - min(t, life) * (cost - salvage) / life`:
charges stop once the useful life is over, so periods after `life` charge
nothing. For `life = 0` no charge is made and the book value is `cost` for every
`t`.
