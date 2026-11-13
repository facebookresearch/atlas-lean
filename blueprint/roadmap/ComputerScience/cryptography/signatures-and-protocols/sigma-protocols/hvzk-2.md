# Special HVZK implies HVZK

Averaging a per-challenge simulator over a uniform challenge
(`uniformChallengeSim`) simulates the honest transcripts, since sampling the coins and the
challenge jointly is sampling the challenge first and then the coins
(`Cslib.Probability.PMF.uniformOfFintype_prod`).
