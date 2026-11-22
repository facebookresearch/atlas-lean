# Floor Book Value

Book value under a salvage-floor depreciation recursion: start at `cost`; in period
`n` charge `charge n v` at current book value `v`, but never write the asset below
`salvage`. Straight-line (`charge n v = c`) and declining-balance (`charge n v = r * v`)
schedules are special cases.
